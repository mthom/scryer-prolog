use prolog_parser_rebis::ast::*;
use prolog_parser_rebis::temp_v;

use crate::fixtures::*;
use crate::forms::*;
use crate::machine::machine_indices::*;
use crate::targets::*;

use std::cell::Cell;
use std::rc::Rc;

pub trait Allocator<'a> {
    fn new() -> Self;

    fn mark_anon_var<Target>(&mut self, _: Level, _: GenContext, _: &mut Vec<Target>)
    where
        Target: CompilationTarget<'a>;
    fn mark_non_var<Target>(
        &mut self,
        _: Level,
        _: GenContext,
        _: &'a Cell<RegType>,
        _: &mut Vec<Target>,
    ) where
        Target: CompilationTarget<'a>;
    fn mark_reserved_var<Target>(
        &mut self,
        _: Rc<Var>,
        _: Level,
        _: &'a Cell<VarReg>,
        _: GenContext,
        _: &mut Vec<Target>,
        _: RegType,
        _: bool,
    ) where
        Target: CompilationTarget<'a>;
    fn mark_var<Target>(
        &mut self,
        _: Rc<Var>,
        _: Level,
        _: &'a Cell<VarReg>,
        _: GenContext,
        _: &mut Vec<Target>,
    ) where
        Target: CompilationTarget<'a>;

    fn reset(&mut self);
    fn reset_contents(&mut self) {}
    fn reset_arg(&mut self, _: usize);
    fn reset_at_head(&mut self, _: &Vec<Box<Term>>);

    fn advance_arg(&mut self);

    fn bindings(&self) -> &AllocVarDict;
    fn bindings_mut(&mut self) -> &mut AllocVarDict;

    fn take_bindings(self) -> AllocVarDict;

    fn drain_var_data(
        &mut self,
        vs: VariableFixtures<'a>,
        num_of_chunks: usize,
    ) -> VariableFixtures<'a> {
        let mut perm_vs = VariableFixtures::new();

        for (var, (var_status, cells)) in vs.into_iter() {
            match var_status {
                VarStatus::Temp(chunk_num, tvd) => {
                    self.bindings_mut()
                        .insert(var.clone(), VarData::Temp(chunk_num, 0, tvd));

                    if chunk_num + 1 == num_of_chunks {
                        perm_vs.insert_last_chunk_temp_var(var);
                    }
                }
                VarStatus::Perm(_) => {
                    self.bindings_mut().insert(var.clone(), VarData::Perm(0));
                    perm_vs.insert(var, (var_status, cells));
                }
            };
        }

        perm_vs
    }

    fn get(&self, var: Rc<Var>) -> RegType {
        self.bindings()
            .get(&var)
            .map_or(temp_v!(0), |v| v.as_reg_type())
    }

    fn is_unbound(&self, var: Rc<Var>) -> bool {
        self.get(var).reg_num() == 0
    }

    fn record_register(&mut self, var: Rc<Var>, r: RegType) {
        match self.bindings_mut().get_mut(&var).unwrap() {
            &mut VarData::Temp(_, ref mut s, _) => *s = r.reg_num(),
            &mut VarData::Perm(ref mut s) => *s = r.reg_num(),
        }
    }
}
