use prolog::ast::*;
use prolog::fixtures::*;

use std::cell::Cell;
use std::cmp::max;
use std::collections::{BTreeSet, HashMap};

pub struct TermMarker<'a> {    
    pub bindings: HashMap<&'a Var, VarData>,
    arg_c:    usize,
    temp_c:   usize,
    contents: HashMap<usize, &'a Var>,
    in_use:   BTreeSet<usize>,
}

impl<'a> TermMarker<'a> {
    pub fn new() -> TermMarker<'a> {
        TermMarker {
            arg_c:    1,
            temp_c:   1,
            bindings: HashMap::new(),
            contents: HashMap::new(),
            in_use: BTreeSet::new()
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

    fn get(&self, var: &'a Var) -> RegType {
        self.bindings.get(var).unwrap().as_reg_type()
    }

    pub fn contains_var(&self, var: &'a Var) -> bool {
        self.bindings.contains_key(var)
    }

    pub fn marked_var(&self, var: &'a Var) -> bool {
        self.get(var).reg_num() != 0
    }

    fn record_register(&mut self, var: &'a Var, r: RegType) {
        match self.bindings.get_mut(var).unwrap() {
            &mut VarData::Temp(_, ref mut s, _) => *s = r.reg_num(),
            &mut VarData::Perm(ref mut s) => *s = r.reg_num()
        }
    }

    pub fn mark_non_var(&mut self, lvl: Level, cell: &Cell<RegType>) {
        let reg_type = cell.get();

        if reg_type.reg_num() == 0 {
            match lvl {
                Level::Deep if !reg_type.is_perm() => {
                    let temp = self.temp_c;
                    self.temp_c += 1;
                    cell.set(RegType::Temp(temp));
                },
                Level::Shallow if !reg_type.is_perm() => {
                    let arg = self.arg_c;
                    self.arg_c += 1;
                    cell.set(RegType::Temp(arg));
                },
                _ => {}
            };
        }
    }

    pub fn mark_old_var(&mut self, lvl: Level, var: &'a Var) -> VarReg
    {
        let inner_reg = self.get(var);

        match lvl {
            Level::Deep => VarReg::Norm(inner_reg),
            Level::Shallow => {
                let reg = VarReg::ArgAndNorm(inner_reg, self.arg_c);
                self.arg_c += 1;
                reg
            }
        }
    }

    pub fn mark_new_var(&mut self, lvl: Level, var: &'a Var, reg: RegType) -> VarReg
    {
        let inner_reg = if !reg.is_perm() {
            let temp = self.temp_c;
            self.temp_c += 1;
            RegType::Temp(temp)
        } else {
            reg
        };

        let reg = match lvl {
            Level::Deep => VarReg::Norm(inner_reg),
            Level::Shallow => {
                let reg = VarReg::ArgAndNorm(inner_reg, self.arg_c);
                self.arg_c += 1;
                reg
            }
        };

        self.record_register(var, inner_reg);
        reg
    }

    pub fn mark_anon_var(&mut self, lvl: Level) -> VarReg {
        let inner_reg = {
            let temp = self.temp_c;
            self.temp_c += 1;
            RegType::Temp(temp)
        };

        match lvl {
            Level::Deep => VarReg::Norm(inner_reg),
            Level::Shallow => {
                let reg = VarReg::ArgAndNorm(inner_reg, self.arg_c);
                self.arg_c += 1;
                reg
            }
        }
    }

    pub fn advance_arg(&mut self) {
        self.arg_c += 1;
    }

    pub fn advance_at_head(&mut self, term: &'a Term) {
        self.arg_c  = 1;
        self.temp_c = max(term.subterms() + 1, self.temp_c);
    }

    pub fn advance(&mut self, term: &'a Term) {
        self.arg_c  = 1;
        self.temp_c = term.subterms() + 1;
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
