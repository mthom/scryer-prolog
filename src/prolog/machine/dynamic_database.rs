use prolog_parser::ast::*;

use prolog::compile::*;
use prolog::heap_print::*;
use prolog::instructions::*;
use prolog::machine::*;
use prolog::machine::machine_errors::*;
use prolog::num::ToPrimitive;

impl Machine {
    fn get_dynamic_predicate_key(&self) -> PredicateKey {
        let name  = self.machine_st[temp_v!(3)].clone();
        let arity = self.machine_st[temp_v!(4)].clone();

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

    fn print_new_dynamic_clause(&self, addrs: VecDeque<Addr>) -> String
    {
        let mut output = PrinterOutputter::new();
        let (name, arity) = self.get_dynamic_predicate_key();

        output.append(format!(":- dynamic({}/{}). ", name.as_str(), arity)
                      .as_str());

        for addr in addrs {
            let mut printer = HCPrinter::new(&self.machine_st, output);
            printer.quoted = true;

            output = printer.print(addr);
            output.append(". ");
        }

        output.result()
    }

    fn handle_eval_result_from_dynamic_compile(&mut self, result: EvalSession)
    {
        if let EvalSession::Error(e) = result {
            println!("{}\r", e);
            self.machine_st.fail = true;
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
                self.print_new_dynamic_clause(addrs)
            },
            Err(err) =>
                return self.machine_st.throw_exception(err)
        };

        let machine_st = mem::replace(&mut self.machine_st, MachineState::new());

        let result = compile_user_module(self, pred_str.as_bytes());
        self.machine_st = machine_st;

        self.handle_eval_result_from_dynamic_compile(result);
    }

    pub(super)
    fn dynamic_transaction(&mut self, trans_type: DynamicTransactionType, p: LocalCodePtr)
    {
        match trans_type {
            DynamicTransactionType::Abolish => {},
            DynamicTransactionType::Assert(place) =>
                self.recompile_dynamic_predicate(place),
            DynamicTransactionType::Retract(idx)  => {}
        }

        self.machine_st.p = CodePtr::Local(p);
    }
}
