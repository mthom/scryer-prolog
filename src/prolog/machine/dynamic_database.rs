use prolog_parser::ast::*;

use prolog::heap_print::*;
use prolog::machine::*;
use prolog::machine::compile::*;
use prolog::machine::machine_errors::*;
use prolog::num::ToPrimitive;

use std::io::Read;

impl Machine {
    pub(super)
    fn atom_tbl_of(&self, name: &ClauseName) -> TabledData<Atom> {
        match name {
            &ClauseName::User(ref rc) => rc.table.clone(),
            _ => self.indices.atom_tbl()
        }
    }

    fn compile_into_machine<R: Read>(&mut self, src: R, name: ClauseName, arity: usize) -> EvalSession
    {
        match name.owning_module().as_str() {
            "user" => compile_user_module(self, src),
            _ => compile_into_module(self, src, name, arity)
        }
    }

    fn get_predicate_key(&self, name: RegType, arity: RegType) -> PredicateKey
    {
        let name  = self.machine_st[name].clone();
        let arity = self.machine_st[arity].clone();

        let name = match self.machine_st.store(self.machine_st.deref(name)) {
            Addr::Con(Constant::Atom(name, _)) => name,
            _ => unreachable!()
        };

        let arity = match self.machine_st.store(self.machine_st.deref(arity)) {
            Addr::Con(Constant::Number(Number::Integer(arity))) =>
                arity.to_usize().unwrap(),
            _ => unreachable!()
        };

        (name, arity)
    }

    fn print_new_dynamic_clause(&self, addrs: VecDeque<Addr>, name: ClauseName, arity: usize)
                                -> String
    {
        let mut output = PrinterOutputter::new();
        output.append(format!(":- dynamic({}/{}). ", name.as_str(), arity).as_str());

        for addr in addrs {
            let mut printer = HCPrinter::new(&self.machine_st, output);
            printer.quoted = true;

            output = printer.print(addr);
            output.append(". ");
        }

        output.result()
    }

    fn abolish_dynamic_clause(&mut self, name: RegType, arity: RegType)
    {
        let (name, arity) = self.get_predicate_key(name, arity);

        if let Some(idx) = self.indices.code_dir.get(&(name.clone(), arity)) {
            set_code_index!(idx, IndexPtr::Undefined, clause_name!("user"));
        }

        self.indices.remove_code_index((name, arity));
    }

    fn abolish_dynamic_clause_in_module(&mut self, name: RegType, arity: RegType, module: RegType)
    {
        let (name, arity) = self.get_predicate_key(name, arity);
        let module_addr = self.machine_st[module].clone();
        
        let module_name = match self.machine_st.store(self.machine_st.deref(module_addr)) {
            Addr::Con(Constant::Atom(module, _)) =>
                match self.indices.modules.get_mut(&module) {
                    Some(ref mut module) => {
                        module.code_dir.remove(&(name.clone(), arity));
                        module.module_decl.name.clone()
                    },
                    _ => {
                        self.machine_st.fail = true;
                        return;
                    }
                },
            _ => unreachable!()
        };
        
        if let Some(idx) = self.indices.code_dir.get(&(name.clone(), arity)) {
            if idx.module_name() == module_name {
                set_code_index!(idx, IndexPtr::Undefined, clause_name!("user"));
            }
        }

        self.indices.remove_code_index((name, arity));
    }
    
    fn handle_eval_result_from_dynamic_compile(&mut self, pred_str: String, name: ClauseName,
                                               arity: usize, src: ClauseName)
    {
        let machine_st = mem::replace(&mut self.machine_st, MachineState::new());

        let result = self.compile_into_machine(pred_str.as_bytes(), name, arity);
        self.machine_st = machine_st;

        if let EvalSession::Error(err) = result {
            let h    = self.machine_st.heap.h;
            let stub = MachineError::functor_stub(src, 1);
            let err  = MachineError::session_error(h, err);
            let err  = self.machine_st.error_form(err, stub);

            self.machine_st.throw_exception(err);
        }
    }

    fn recompile_dynamic_predicate_impl(&mut self, place: DynamicAssertPlace, name: ClauseName,
                                        arity: usize)
    {
        let stub = MachineError::functor_stub(place.predicate_name(), 1);
        let pred_str = match self.machine_st.try_from_list(temp_v!(2), stub) {
            Ok(addrs) => {
                let mut addrs = VecDeque::from(addrs);
                let added_clause = self.machine_st[temp_v!(1)].clone();

                place.push_to_queue(&mut addrs, added_clause);
                self.print_new_dynamic_clause(addrs, name.clone(), arity)
            },
            Err(err) =>
                return self.machine_st.throw_exception(err)
        };

        self.handle_eval_result_from_dynamic_compile(pred_str, name, arity, place.predicate_name());
    }

    fn set_module_atom_tbl(&mut self, module_addr: Addr, name: &mut ClauseName) -> bool
    {
        let atom_tbl = match self.machine_st.store(self.machine_st.deref(module_addr)) {
            Addr::Con(Constant::Atom(module, _)) =>
                match self.indices.modules.get(&module) {
                    Some(ref module) => module.atom_tbl.clone(),
                    None => {
                        self.machine_st.fail = true;
                        return false;
                    }
                },
            _ => unreachable!()
        };

        if let &mut ClauseName::User(ref mut rc) = name {
            rc.table = atom_tbl;
        }

        true
    }

    fn recompile_dynamic_predicate_in_module(&mut self, place: DynamicAssertPlace)
    {
        let (mut name, arity) = self.get_predicate_key(temp_v!(3), temp_v!(4));
        let module_addr = self.machine_st[temp_v!(5)].clone();

        if self.set_module_atom_tbl(module_addr, &mut name) {
            self.recompile_dynamic_predicate_impl(place, name, arity);
        }
    }

    fn recompile_dynamic_predicate(&mut self, place: DynamicAssertPlace)
    {
        let (name, arity) = self.get_predicate_key(temp_v!(3), temp_v!(4));
        self.recompile_dynamic_predicate_impl(place, name, arity);
    }

    fn retract_from_dynamic_predicate_in_module(&mut self)
    {
        let index = self.machine_st[temp_v!(3)].clone();
        let index = match self.machine_st.store(self.machine_st.deref(index)) {
            Addr::Con(Constant::Number(Number::Integer(n))) => n.to_usize().unwrap(),
            _ => unreachable!()
        };

        let (mut name, arity) = self.get_predicate_key(temp_v!(1), temp_v!(2));
        let module_addr = self.machine_st[temp_v!(5)].clone();

        if self.set_module_atom_tbl(module_addr, &mut name) {
            self.retract_from_dynamic_predicate_impl(name, arity, index);
        }
    }

    fn retract_from_dynamic_predicate(&mut self)
    {
        let index = self.machine_st[temp_v!(3)].clone();
        let index = match self.machine_st.store(self.machine_st.deref(index)) {
            Addr::Con(Constant::Number(Number::Integer(n))) => n.to_usize().unwrap(),
            _ => unreachable!()
        };
        
        let (name, arity) = self.get_predicate_key(temp_v!(1), temp_v!(2));

        self.retract_from_dynamic_predicate_impl(name, arity, index);
    }

    fn retract_from_dynamic_predicate_impl(&mut self, name: ClauseName, arity: usize, index: usize)
    {
        let stub = MachineError::functor_stub(clause_name!("retract"), 1);
        let pred_str = match self.machine_st.try_from_list(temp_v!(4), stub) {
            Ok(addrs) => {
                let mut addrs = VecDeque::from(addrs);
                addrs.remove(index);

                if addrs.is_empty() {
                    self.abolish_dynamic_clause(temp_v!(1), temp_v!(2));
                    return;
                }

                self.print_new_dynamic_clause(addrs, name.clone(), arity)
            },
            Err(err) =>
                return self.machine_st.throw_exception(err)
        };

        self.handle_eval_result_from_dynamic_compile(pred_str, name, arity, clause_name!("retract"));
    }

    pub(super)
    fn dynamic_transaction(&mut self, trans_type: DynamicTransactionType, p: LocalCodePtr)
    {
        match trans_type {
            DynamicTransactionType::Abolish =>
                self.abolish_dynamic_clause(temp_v!(1), temp_v!(2)),
            DynamicTransactionType::Assert(place) =>
                self.recompile_dynamic_predicate(place),
            DynamicTransactionType::ModuleAbolish =>
                self.abolish_dynamic_clause_in_module(temp_v!(1), temp_v!(2), temp_v!(3)),
            DynamicTransactionType::ModuleAssert(place) =>
                self.recompile_dynamic_predicate_in_module(place),
            DynamicTransactionType::ModuleRetract =>
                self.retract_from_dynamic_predicate_in_module(),
            DynamicTransactionType::Retract =>
                self.retract_from_dynamic_predicate()
        }

        self.machine_st.p = CodePtr::Local(p);
    }
}
