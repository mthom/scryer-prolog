use prolog::ast::*;
use prolog::fixtures::*;
use prolog::targets::*;

use std::cell::Cell;

pub trait Allocator<'a>
{
    fn new() -> Self;
    
    fn mark_anon_var<Target>(&mut self, Level, &mut Vec<Target>)
        where Target: CompilationTarget<'a>;
    fn mark_non_var<Target>(&mut self, Level, GenContext, &'a Cell<RegType>, &mut Vec<Target>)
        where Target: CompilationTarget<'a>;
    fn mark_var<Target>(&mut self, &'a Var, Level, &'a Cell<VarReg>, GenContext, &mut Vec<Target>)
        where Target: CompilationTarget<'a>;    
    
    fn reset(&mut self);
    fn reset_contents(&mut self) {}

    fn advance(&mut self, GenContext, QueryTermRef<'a>);
    fn advance_arg(&mut self);

    fn bindings(&self) -> &AllocVarDict<'a>;
    fn bindings_mut(&mut self) -> &mut AllocVarDict<'a>;

    fn take_bindings(self) -> AllocVarDict<'a>;

    fn drain_var_data(&mut self, vs: VariableFixtures<'a>) -> VariableFixtures<'a>
    {
        let mut perm_vs = VariableFixtures::new();

        for (var, (var_status, cells)) in vs.into_iter() {
            match var_status {
                VarStatus::Temp(chunk_num, tvd) => {
                    self.bindings_mut().insert(var, VarData::Temp(chunk_num, 0, tvd));
                },
                VarStatus::Perm(_) => {
                    self.bindings_mut().insert(var, VarData::Perm(0));
                    perm_vs.insert(var, (var_status, cells));
                }
            };
        }

        perm_vs
    }
    
    fn get(&self, var: &'a Var) -> RegType {
        self.bindings().get(var).unwrap().as_reg_type()
    }    
    
    fn record_register(&mut self, var: &'a Var, r: RegType) {
        match self.bindings_mut().get_mut(var).unwrap() {
            &mut VarData::Temp(_, ref mut s, _) => *s = r.reg_num(),
            &mut VarData::Perm(ref mut s) => *s = r.reg_num()
        }
    }
}
