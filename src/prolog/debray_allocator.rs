use prolog::ast::*;
use prolog::fixtures::*;
use prolog::targets::*;

use std::cell::Cell;
use std::collections::{BTreeSet, HashMap};

pub struct TermMarker<'a> {
    pub bindings: HashMap<&'a Var, VarData>,
    arg_c:    usize,
    temp_lb:  usize,
    contents: HashMap<usize, &'a Var>,
    in_use:   BTreeSet<usize>,
}

impl<'a> TermMarker<'a> {
    pub fn new() -> TermMarker<'a> {
        TermMarker {
            arg_c:   1,
            temp_lb: 1,
            bindings: HashMap::new(),
            contents: HashMap::new(),
            in_use: BTreeSet::new()
        }
    }

    fn occurs_shallowly_in_head(&self, var: &'a Var, term_loc: GenContext, r: usize) -> bool
    {
        match (term_loc, self.bindings.get(var).unwrap()) {
            (GenContext::Head, &VarData::Temp(_, _, ref tvd)) =>
                tvd.use_set.contains(&(GenContext::Head, r)),
            _ => false
        }
    }

    pub fn drain_var_data(&mut self, vs: VariableFixtures<'a>) -> VariableFixtures<'a>
    {
        let mut perm_vs = VariableFixtures::new();

        for (var, (var_status, cells)) in vs.into_iter() {
            match var_status {
                VarStatus::Temp(chunk_num, tvd) => {
                    self.bindings.insert(var, VarData::Temp(chunk_num, 0, tvd));
                },
                VarStatus::Perm(_) => {
                    self.bindings.insert(var, VarData::Perm(0));
                    perm_vs.insert(var, (var_status, cells));
                }
            };
        }

        perm_vs
    }

    fn alloc_with_cr(&self, var: &'a Var) -> usize
    {
        match self.bindings.get(var) {
            Some(&VarData::Temp(_, _, ref tvd)) => {
                for &(_, reg) in tvd.use_set.iter() {
                    if !self.in_use.contains(&reg) {
                        return reg;
                    }
                }

                let mut result = 0;

                for reg in self.temp_lb .. {
                    if !self.in_use.contains(&reg) {
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

    fn alloc_with_ca(&self, var: &'a Var) -> usize
    {
        match self.bindings.get(var) {
            Some(&VarData::Temp(_, _, ref tvd)) => {
                for &(_, reg) in tvd.use_set.iter() {
                    if !self.in_use.contains(&reg) {
                        return reg;
                    }
                }

                let mut result = 0;

                for reg in self.temp_lb .. {
                    if !self.in_use.contains(&reg) {
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

    fn alloc_in_last_goal_hint(&self, chunk_num: usize) -> Option<(&'a Var, usize)>
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
                        return Some((t_var, self.alloc_with_ca(t_var)));
                    }
                }

                None
            },
            _ => None
        }
    }

    fn evacuate_arg<Target>(&mut self, chunk_num: usize, target: &mut Vec<Target>)
        where Target: CompilationTarget<'a>
    {
        match self.alloc_in_last_goal_hint(chunk_num) {
            Some((var, r)) => {
                let k = self.arg_c;

                if r != k {
                    let r = RegType::Temp(r);

                    if r.reg_num() != k {
                        target.push(Target::move_to_register(r, k));

                        self.contents.remove(&k);
                        self.contents.insert(r.reg_num(), var);

                        self.record_register(var, r);
                        self.in_use.insert(r.reg_num());
                    }
                }
            },
            _ => {}
        };
    }

    fn alloc_reg_to_var<Target>(&mut self,
                                var: &'a Var,
                                lvl: Level,
                                term_loc: GenContext,
                                target: &mut Vec<Target>)
                                -> usize
        where Target: CompilationTarget<'a>
    {
        match term_loc {
            GenContext::Head =>
                if let Level::Shallow = lvl {
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

    fn get(&self, var: &'a Var) -> RegType {
        self.bindings.get(var).unwrap().as_reg_type()
    }

    fn in_place(&self, var: &'a Var, term_loc: GenContext, r: RegType, k: usize) -> bool
    {
        match term_loc {
            GenContext::Head if !r.is_perm() => r.reg_num() == k,
            _ => match self.bindings.get(var).unwrap() {
                     &VarData::Temp(_, o, _) if r.reg_num() == k => o == k,
                     _ => false
                 }
        }
    }

    // delete after anon_vars are handled by means of *_void stuff.
    pub fn mark_anon_var<Target>(&mut self, lvl: Level, target: &mut Vec<Target>)
        where Target: CompilationTarget<'a>
    {
        let r = RegType::Temp(self.alloc_reg_to_non_var());

        match lvl {
            Level::Shallow => {
                let k = self.arg_c;
                self.arg_c += 1;

                target.push(Target::argument_to_variable(r, k));
            },
            Level::Deep =>
                target.push(Target::subterm_to_variable(r))
        };
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

    pub fn mark_non_var<Target>(&mut self,
                                lvl: Level,
                                term_loc: GenContext,
                                cell: &Cell<RegType>,
                                target: &mut Vec<Target>)
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

    pub fn mark_var<Target>(&mut self,
                            var: &'a Var,
                            lvl: Level,
                            cell: &'a Cell<VarReg>,
                            term_loc: GenContext,
                            target: &mut Vec<Target>)
        where Target: CompilationTarget<'a>
    {
        let (r, is_new_var) = match self.get(var) {
            RegType::Temp(0) => {
                // here, r is temporary *and* unassigned.
                let o = self.alloc_reg_to_var(var, lvl, term_loc, target);

                cell.set(VarReg::Norm(RegType::Temp(o)));

                (RegType::Temp(o), true)
            },
            RegType::Perm(0) => {
                let pr = cell.get().norm();
                self.record_register(var, pr);
                (pr, true)
            },
            r => (r, false)
        };

        match lvl {
            Level::Shallow => {
                let k = self.arg_c;
                self.arg_c += 1;

                cell.set(VarReg::ArgAndNorm(r, k));

                if !self.in_place(var, term_loc, r, k) {
                    if is_new_var {
                        target.push(Target::argument_to_variable(r, k));
                    } else {
                        target.push(Target::argument_to_value(r, k));
                    }
                }
            },
            Level::Deep if is_new_var =>
                if self.occurs_shallowly_in_head(var, term_loc, r.reg_num()) {
                    target.push(Target::subterm_to_value(r));
                } else {
                    target.push(Target::subterm_to_variable(r));
                },
            Level::Deep =>
                target.push(Target::subterm_to_value(r))
        };

        if !r.is_perm() {
            let o = r.reg_num();

            self.contents.insert(o, var);
            self.record_register(var, r);
            self.in_use.insert(o);
        }
    }

    pub fn contains_var(&self, var: &'a Var) -> bool {
        self.bindings.contains_key(var)
    }

    fn record_register(&mut self, var: &'a Var, r: RegType) {
        match self.bindings.get_mut(var).unwrap() {
            &mut VarData::Temp(_, ref mut s, _) => *s = r.reg_num(),
            &mut VarData::Perm(ref mut s) => *s = r.reg_num()
        }
    }

    pub fn advance_arg(&mut self) {
        self.arg_c += 1;
    }

    pub fn advance(&mut self, term: &'a Term) {
        self.arg_c = 1;
        self.temp_lb = term.arity() + 1;
    }

    pub fn reset(&mut self) {
        self.bindings.clear();
        self.contents.clear();
        self.in_use.clear();
    }

    pub fn reset_contents(&mut self) {
        self.contents.clear();
        self.in_use.clear();
    }
}
