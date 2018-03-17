use prolog::allocator::*;
use prolog::ast::*;
use prolog::targets::*;

use std::cell::Cell;
use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

pub struct DebrayAllocator {
    bindings: HashMap<Rc<Var>, VarData>,
    arg_c:    usize,
    temp_lb:  usize,
    arity:    usize, // 0 if not at head.
    contents: HashMap<usize, Rc<Var>>,
    in_use:   BTreeSet<usize>,
}

impl DebrayAllocator {
    fn is_curr_arg_distinct_from(&self, var: &Var) -> bool {
        match self.contents.get(&self.arg_c) {
            Some(t_var) if **t_var != *var => true,
            _ => false
        }
    }

    fn occurs_shallowly_in_head(&self, var: &Var, r: usize) -> bool
    {
        match self.bindings.get(var).unwrap() {
            &VarData::Temp(_, _, ref tvd) =>
                tvd.use_set.contains(&(GenContext::Head, r)),
            _ => false
        }
    }

    fn is_in_use(&self, r: usize) -> bool {
        let in_use_range = r <= self.arity && r >= self.arg_c;
        in_use_range || self.in_use.contains(&r)
    }

    fn alloc_with_cr(&self, var: &Var) -> usize
    {
        match self.bindings.get(var) {
            Some(&VarData::Temp(_, _, ref tvd)) => {
                for &(_, reg) in tvd.use_set.iter() {
                    if !self.is_in_use(reg) {
                        return reg;
                    }
                }

                let mut result = 0;

                for reg in self.temp_lb .. {
                    if !self.is_in_use(reg) {
                        if !tvd.no_use_set.contains(&reg) {
                            result = reg;
                            break;
                        }
                    }
                }

                result
            },
            _ => 0
        }
    }

    fn alloc_with_ca(&self, var: &Var) -> usize
    {
        match self.bindings.get(var) {
            Some(&VarData::Temp(_, _, ref tvd)) => {
                for &(_, reg) in tvd.use_set.iter() {
                    if !self.is_in_use(reg) {
                        return reg;
                    }
                }

                let mut result = 0;

                for reg in self.temp_lb .. {
                    if !self.is_in_use(reg) {
                        if !tvd.no_use_set.contains(&reg) {
                            if !tvd.conflict_set.contains(&reg) {
                                result = reg;
                                break;
                            }
                        }
                    }
                }

                result
            },
            _ => 0
        }
    }

    fn alloc_in_last_goal_hint(&self, chunk_num: usize) -> Option<(Rc<Var>, usize)>
    {
        // we want to allocate a register to the k^{th} parameter, par_k.
        // par_k may not be a temporary variable.
        let k = self.arg_c;

        match self.contents.get(&k) {
            Some(t_var) => {
                // suppose this branch fires. then t_var is a
                // temp. var. belonging to the current chunk.
                // consider its use set. T == par_k iff
                // (GenContext::Last(_), k) is in t_var.use_set.

                let tvd = self.bindings.get(t_var).unwrap();
                if let &VarData::Temp(_, _, ref tvd) = tvd {
                    if !tvd.use_set.contains(&(GenContext::Last(chunk_num), k)) {
                        return Some((t_var.clone(), self.alloc_with_ca(t_var)));
                    }
                }

                None
            },
            _ => None
        }
    }

    fn evacuate_arg<'a, Target>(&mut self, chunk_num: usize, target: &mut Vec<Target>)
        where Target: CompilationTarget<'a>
    {
        match self.alloc_in_last_goal_hint(chunk_num) {
            Some((var, r)) => {
                let k = self.arg_c;

                if r != k {
                    let r = RegType::Temp(r);

                    target.push(Target::move_to_register(r, k));

                    self.contents.remove(&k);
                    self.contents.insert(r.reg_num(), var.clone());

                    self.record_register(var, r);
                    self.in_use.insert(r.reg_num());
                }
            },
            _ => {}
        };
    }

    fn alloc_reg_to_var<'a, Target>(&mut self, var: &Var, lvl: Level, term_loc: GenContext,
                                    target: &mut Vec<Target>)
                                -> usize
        where Target: CompilationTarget<'a>
    {
        match term_loc {
            GenContext::Head =>
                if let Level::Shallow = lvl {
                    self.evacuate_arg(0, target);
                    self.alloc_with_cr(var)
                } else {
                    self.alloc_with_ca(var)
                },
            GenContext::Mid(_) =>
                self.alloc_with_ca(var),
            GenContext::Last(chunk_num) =>
                if let Level::Shallow = lvl {
                    self.evacuate_arg(chunk_num, target);
                    self.alloc_with_cr(var)
                } else {
                    self.alloc_with_ca(var)
                }
        }
    }

    fn alloc_reg_to_non_var(&mut self) -> usize
    {
        let mut final_index = 0;

        for index in self.temp_lb .. {
            if !self.in_use.contains(&index) {
                final_index = index;
                break;
            }
        }

        self.temp_lb = final_index + 1;

        final_index
    }

    fn in_place(&self, var: &Var, term_loc: GenContext, r: RegType, k: usize) -> bool
    {
        match term_loc {
            GenContext::Head if !r.is_perm() => r.reg_num() == k,
            _ => match self.bindings().get(var).unwrap() {
                     &VarData::Temp(_, o, _) if r.reg_num() == k => o == k,
                     _ => false
                 }
        }
    }
}

impl<'a> Allocator<'a> for DebrayAllocator
{
    fn new() -> DebrayAllocator {
        DebrayAllocator {
            arity:   0,
            arg_c:   1,
            temp_lb: 1,
            bindings: HashMap::new(),
            contents: HashMap::new(),
            in_use: BTreeSet::new()
        }
    }

    fn mark_anon_var<Target>(&mut self, lvl: Level, target: &mut Vec<Target>)
        where Target: CompilationTarget<'a>
    {
        let r = RegType::Temp(self.alloc_reg_to_non_var());

        match lvl {
            Level::Deep => target.push(Target::subterm_to_variable(r)),
            Level::Root | Level::Shallow => {
                let k = self.arg_c;
                self.arg_c += 1;

                target.push(Target::argument_to_variable(r, k));
            }
        };
    }

    fn mark_non_var<Target>(&mut self, lvl: Level, term_loc: GenContext,
                            cell: &Cell<RegType>, target: &mut Vec<Target>)
        where Target: CompilationTarget<'a>
    {
        let r = cell.get();

        if r.reg_num() == 0 {
            let r = match lvl {
                Level::Shallow => {
                    let k = self.arg_c;

                    if let GenContext::Last(chunk_num) = term_loc {
                        self.evacuate_arg(chunk_num, target);
                    }

                    self.arg_c += 1;
                    RegType::Temp(k)
                },
                _ => RegType::Temp(self.alloc_reg_to_non_var())
            };

            cell.set(r);
        }
    }

    fn mark_var<Target>(&mut self, var: Rc<Var>, lvl: Level, cell: &Cell<VarReg>,
                        term_loc: GenContext, target: &mut Vec<Target>)
        where Target: CompilationTarget<'a>
    {
        let (r, is_new_var) = match self.get(var.clone()) {
            RegType::Temp(0) => {
                // here, r is temporary *and* unassigned.
                let o = self.alloc_reg_to_var(&var, lvl, term_loc, target);

                cell.set(VarReg::Norm(RegType::Temp(o)));

                (RegType::Temp(o), true)
            },
            RegType::Perm(0) => {
                let pr = cell.get().norm();
                self.record_register(var.clone(), pr);

                (pr, true)
            },
            r => (r, false)
        };

        match lvl {
            Level::Root | Level::Shallow => {
                let k = self.arg_c;

                if self.is_curr_arg_distinct_from(&var) {
                    self.evacuate_arg(term_loc.chunk_num(), target);
                }

                self.arg_c += 1;

                cell.set(VarReg::ArgAndNorm(r, k));

                if !self.in_place(&var, term_loc, r, k) {
                    if is_new_var {
                        target.push(Target::argument_to_variable(r, k));
                    } else {
                        target.push(Target::argument_to_value(r, k));
                    }
                }
            },
            Level::Deep if is_new_var =>
                if let GenContext::Head = term_loc {
                    if self.occurs_shallowly_in_head(&var, r.reg_num()) {
                        target.push(Target::subterm_to_value(r));
                    } else {
                        target.push(Target::subterm_to_variable(r));
                    }
                } else {
                    target.push(Target::subterm_to_variable(r));
                },
            Level::Deep =>
                target.push(Target::subterm_to_value(r))
        };

        if !r.is_perm() {
            let o = r.reg_num();

            self.contents.insert(o, var.clone());
            self.record_register(var.clone(), r);
            self.in_use.insert(o);
        }
    }

    fn reset(&mut self) {
        self.bindings.clear();
        self.contents.clear();
        self.in_use.clear();
    }

    fn reset_contents(&mut self) {
        self.contents.clear();
        self.in_use.clear();
    }

    fn advance_arg(&mut self) {
        self.arg_c += 1;
    }

    fn bindings(&self) -> &AllocVarDict {
        &self.bindings
    }

    fn bindings_mut(&mut self) -> &mut AllocVarDict {
        &mut self.bindings
    }

    fn take_bindings(self) -> AllocVarDict {
        self.bindings
    }

    fn reset_at_head(&mut self, args: &Vec<Box<Term>>) {
        self.reset_arg(args.len());
        self.arity = args.len();

        for (idx, arg) in args.iter().enumerate() {
            if let &Term::Var(_, ref var) = arg.as_ref() {
                let r = self.get(var.clone());

                if !r.is_perm() && r.reg_num() == 0 {
                    self.in_use.insert(idx + 1);
                    self.contents.insert(idx + 1, var.clone());
                    self.record_register(var.clone(), temp_v!(idx + 1));
                }
            }
        }
    }

    fn reset_arg(&mut self, arity: usize) {
        self.arity   = 0;
        self.arg_c   = 1;
        self.temp_lb = arity + 1;
    }
}
