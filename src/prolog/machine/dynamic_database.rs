use prolog_parser::ast::*;

use prolog::compile::*;
use prolog::heap_print::*;
use prolog::instructions::*;
use prolog::machine::*;
use prolog::machine::machine_errors::*;
use prolog::num::ToPrimitive;

impl Machine {
    fn get_predicate_key(&self, name: RegType, arity: RegType) -> PredicateKey {
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

    fn print_new_dynamic_clause(&self, addrs: VecDeque<Addr>, name: RegType, arity: RegType)
                                -> String
    {
        let mut output = PrinterOutputter::new();
        let (name, arity) = self.get_predicate_key(name, arity);

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

        self.indices.code_dir.remove(&(name.clone(), arity));
        self.indices.dynamic_code_dir.remove(&(name, arity));
    }

    fn handle_eval_result_from_dynamic_compile(&mut self, pred_str: String, src: ClauseName)
    {
        let machine_st = mem::replace(&mut self.machine_st, MachineState::new());
        let result = compile_user_module(self, pred_str.as_bytes());

        self.machine_st = machine_st;

        if let EvalSession::Error(err) = result {
            let h    = self.machine_st.heap.h;
            let stub = MachineError::functor_stub(src, 1);
            let err  = MachineError::session_error(h, err);
            let err  = self.machine_st.error_form(err, stub);            

            self.machine_st.throw_exception(err);
        }
    }

    fn recompile_dynamic_predicate(&mut self, place: DynamicAssertPlace)
    {
        let stub = MachineError::functor_stub(place.predicate_name(), 1);
        let pred_str = match self.machine_st.try_from_list(temp_v!(2), stub) {
            Ok(addrs) => {
                let mut addrs = VecDeque::from(addrs);
                let added_clause = self.machine_st[temp_v!(1)].clone();

                place.push_to_queue(&mut addrs, added_clause);
                self.print_new_dynamic_clause(addrs, temp_v!(3), temp_v!(4))
            },
            Err(err) =>
                return self.machine_st.throw_exception(err)
        };

        self.handle_eval_result_from_dynamic_compile(pred_str, place.predicate_name());
    }

    fn retract_from_dynamic_predicate(&mut self) {
        let index = self.machine_st[temp_v!(3)].clone();
        let index = match self.machine_st.store(self.machine_st.deref(index)) {
            Addr::Con(Constant::Number(Number::Integer(n))) => n.to_usize().unwrap(),
            _ => unreachable!()
        };

        let stub = MachineError::functor_stub(clause_name!("retract"), 1);
        let pred_str = match self.machine_st.try_from_list(temp_v!(4), stub) {
            Ok(addrs) => {
                let mut addrs = VecDeque::from(addrs);
                addrs.remove(index);

                if addrs.is_empty() {
                    self.abolish_dynamic_clause(temp_v!(1), temp_v!(2));
                    return;
                }

                self.print_new_dynamic_clause(addrs, temp_v!(1), temp_v!(2))
            },
            Err(err) =>
                return self.machine_st.throw_exception(err)
        };

        self.handle_eval_result_from_dynamic_compile(pred_str, clause_name!("retract"));
    }

    pub(super)
    fn dynamic_transaction(&mut self, trans_type: DynamicTransactionType, p: LocalCodePtr)
    {
        match trans_type {
            DynamicTransactionType::Abolish =>
                self.abolish_dynamic_clause(temp_v!(1), temp_v!(2)),
            DynamicTransactionType::Assert(place) =>
                self.recompile_dynamic_predicate(place),
            DynamicTransactionType::Retract =>
                self.retract_from_dynamic_predicate()
        }

        self.machine_st.p = CodePtr::Local(p);
    }
}
