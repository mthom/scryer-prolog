use prolog::machine::*;

pub static VERIFY_ATTRS: &str = "
iterate([Var|VarBindings], [Value|ValueBindings]) :-
    '$get_attr_list'(Var, Ls),
    call_verify_attributes(Ls, Var, Value),
    iterate(VarBindings, ValueBindings).
iterate([], []) :- '$restore_p_from_sfcp'.

call_verify_attributes(Attrs, _, _) :-
    var(Attrs), !.
call_verify_attributes([Attr|Attrs], Var, Value) :-
    '$module_of'(M, Attr), % write the owning module Attr to M.
    catch(M:verify_attributes(Var, Value, Goals),
          error(evaluation_error((M:verify_attributes)/3), verify_attributes/3),
          true),
    call_verify_attributes_goals(Goals),
    call_verify_attributes(Attrs, Var, Value).

call_verify_attributes_goals(Goals) :-
    var(Goals), throw(error(instantiation_error, call_verify_attributes_goals/1)).
call_verify_attributes_goals([Goal|Goals]) :-
    call(Goal), !, call_verify_attributes_goals(Goals).
call_verify_attributes_goals([]).
";

pub(super) type Bindings = Vec<(usize, Addr)>;

pub(super) struct AttrVarInitializer {
    pub(super) bindings: Bindings,
    pub(super) registers: Registers,
    pub(super) special_form_cp: CodePtr,
    pub(super) verify_attrs_loc: usize
}

impl AttrVarInitializer {
    pub(super) fn new(p: usize) -> Self {
        AttrVarInitializer {
            bindings: vec![],
            verify_attrs_loc: p,
            special_form_cp: CodePtr::VerifyAttrInterrupt(p),
            registers: vec![Addr::HeapCell(0); MAX_ARITY + 1]
        }
    }

    pub(super) fn reset(&mut self) {
        self.special_form_cp = CodePtr::VerifyAttrInterrupt(self.verify_attrs_loc);
    }
}

impl MachineState {
    pub(super) fn add_attr_var_binding(&mut self, h: usize, addr: Addr)
    {
        self.attr_var_init.bindings.push((h, addr));

        if let &CodePtr::VerifyAttrInterrupt(_) = &self.p {
            return;
        }

        mem::swap(&mut self.attr_var_init.special_form_cp, &mut self.p);
        self.attr_var_init.special_form_cp += 1;
    }

    pub(super)
    fn verify_attributes(&mut self)
    {
        /* STEP 1: Undo bindings in machine.
           STEP 2: Write the list of bindings to two lists in the heap, one for vars, one for values.
           STEP 3: Swap the machine's Registers for attr_var_init's Registers.
           STEP 4: Pass the addresses of the lists to iterate in the attr_vars special form.
           STEP 5: Restore AttrVarInitializer::special_form_cp to self.p.
           STEP 6: Swap the bindings' Registers back for the machine's Registers.
           STEP 7: Redo the bindings.
           STEP 8: Continue.
         */

        for (h, _) in &self.attr_var_init.bindings {
            self.heap[*h] = HeapCellValue::Addr(Addr::AttrVar(*h));
        }

        let (var_list_addr, value_list_addr) = {
            let iter = self.attr_var_init.bindings.iter().map(|(ref h, _)| Addr::AttrVar(*h));
            let var_list_addr = Addr::HeapCell(self.heap.to_list(iter));

            let iter = self.attr_var_init.bindings.iter().map(|(_, ref addr)| addr.clone());
            let value_list_addr = Addr::HeapCell(self.heap.to_list(iter));

            (var_list_addr, value_list_addr)
        };

        mem::swap(&mut self.registers, &mut self.attr_var_init.registers);

        self[temp_v!(1)] = var_list_addr;
        self[temp_v!(2)] = value_list_addr;
    }
}
