use crate::parser::ast::*;
use crate::temp_v;

use crate::fixtures::*;
use crate::forms::*;
use crate::instructions::*;
use crate::machine::machine_indices::*;
use crate::targets::*;

use std::cell::Cell;

pub(crate) trait Allocator {
    fn new() -> Self;

    fn mark_anon_var<'a, Target: CompilationTarget<'a>>(
        &mut self,
        lvl: Level,
        context: GenContext,
        code: &mut Code,
    );

    fn mark_non_var<'a, Target: CompilationTarget<'a>>(
        &mut self,
        lvl: Level,
        context: GenContext,
        cell: &'a Cell<RegType>,
        code: &mut Code,
    );

    fn mark_reserved_var<'a, Target: CompilationTarget<'a>>(
        &mut self,
        var_name: Var,
        lvl: Level,
        cell: &'a Cell<VarReg>,
        term_loc: GenContext,
        code: &mut Code,
        r: RegType,
        is_new_var: bool,
    );

    fn mark_var<'a, Target: CompilationTarget<'a>>(
        &mut self,
        var_name: Var,
        lvl: Level,
        cell: &'a Cell<VarReg>,
        context: GenContext,
        code: &mut Code,
    );

    fn reset(&mut self);
    fn reset_contents(&mut self) {}
    fn reset_arg(&mut self, arg_num: usize);
    fn reset_at_head(&mut self, args: &Vec<Term>);

    fn advance_arg(&mut self);

    fn bindings(&self) -> &AllocVarDict;
    fn bindings_mut(&mut self) -> &mut AllocVarDict;

    fn take_bindings(self) -> AllocVarDict;
    fn max_reg_allocated(&self) -> usize;

    // TODO: wha.. why?? grrr. it drains the VarStatus data from vs (which it owns!)
    // into self.bindings and perm_vs after all is computed (i.e. vs.populate_restricting_sets()
    // and vs.set_perm_vals(has_deep_cut) have both been called).
    /*
    fn drain_var_data<'a>(
        &mut self,
        vs: VariableFixtures,
        num_of_chunks: usize,
    ) -> VariableFixtures {
        let mut perm_vs = VariableFixtures::new();

        for (var, var_status) in vs.into_iter() {
            match var_status {
                VarStatus::Temp(chunk_num, tvd) => {
                    self.bindings_mut()
                        .insert(var.clone(), VarAlloc::Temp(chunk_num, 0, tvd));
                }
                VarStatus::Perm(_) => {
                    self.bindings_mut().insert(var.clone(), VarAlloc::Perm(0));
                    perm_vs.insert(var, var_status);
                }
            };
        }

        perm_vs
    }
    */

    fn get(&self, var: Var) -> RegType {
        self.bindings()
            .get(&var)
            .map_or(temp_v!(0), |v| v.as_reg_type())
    }

    fn is_unbound(&self, var: Var) -> bool {
        self.get(var).reg_num() == 0
    }

    fn record_register(&mut self, var: Var, r: RegType) {
        match self.bindings_mut().get_mut(&var).unwrap() {
            &mut VarAlloc::Temp(_, ref mut s, _) => *s = r.reg_num(),
            &mut VarAlloc::Perm(ref mut s) => *s = r.reg_num(),
        }
    }
}
