use prolog::ast::*;
use prolog::fixtures::*;
use prolog::targets::*;

use std::cell::Cell;
use std::rc::Rc;

pub trait Allocator<'a>
{
    fn new() -> Self;

    fn mark_anon_var<Target>(&mut self, Level, &mut Vec<Target>)
        where Target: CompilationTarget<'a>;
    fn mark_non_var<Target>(&mut self, Level, GenContext, &'a Cell<RegType>, &mut Vec<Target>)
        where Target: CompilationTarget<'a>;
    fn mark_reserved_var<Target>(&mut self, Rc<Var>, Level, &'a Cell<VarReg>, GenContext,
                                 &mut Vec<Target>, RegType, bool)
        where Target: CompilationTarget<'a>;
    fn mark_var<Target>(&mut self, Rc<Var>, Level, &'a Cell<VarReg>, GenContext, &mut Vec<Target>)
        where Target: CompilationTarget<'a>;

    fn reset(&mut self);
    fn reset_contents(&mut self) {}
    fn reset_arg(&mut self, usize);
    fn reset_at_head(&mut self, &Vec<Box<Term>>);

    fn advance_arg(&mut self);

    fn bindings(&self) -> &AllocVarDict;
    fn bindings_mut(&mut self) -> &mut AllocVarDict;

    fn take_bindings(self) -> AllocVarDict;

    fn drain_var_data(&mut self, vs: VariableFixtures<'a>) -> VariableFixtures<'a>
    {
        let mut perm_vs = VariableFixtures::new();

        for (var, (var_status, cells)) in vs.into_iter() {
            match var_status {
                VarStatus::Temp(chunk_num, tvd) => {
                    self.bindings_mut().insert(var.clone(), VarData::Temp(chunk_num, 0, tvd));
                },
                VarStatus::Perm(_) => {
                    self.bindings_mut().insert(var.clone(), VarData::Perm(0));
                    perm_vs.insert(var, (var_status, cells));
                }
            };
        }

        perm_vs
    }

    fn get(&self, var: Rc<Var>) -> RegType {
        self.bindings().get(&var).map_or(temp_v!(0), |v| v.as_reg_type())
    }

    fn is_unbound(&self, var: Rc<Var>) -> bool {
        self.get(var).reg_num() == 0
    }

    fn record_register(&mut self, var: Rc<Var>, r: RegType) {
        match self.bindings_mut().get_mut(&var).unwrap() {
            &mut VarData::Temp(_, ref mut s, _) => *s = r.reg_num(),
            &mut VarData::Perm(ref mut s) => *s = r.reg_num()
        }
    }
}
