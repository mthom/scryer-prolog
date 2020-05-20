use prolog_parser::ast::*;
use prolog_parser::parser::*;
use prolog_parser::tabled_rc::*;

use crate::prolog::clause_types::*;
use crate::prolog::forms::*;
use crate::prolog::heap_print::*;
use crate::prolog::instructions::*;
use crate::prolog::machine::code_repo::CodeRepo;
use crate::prolog::machine::copier::*;
use crate::prolog::machine::code_walker::*;
use crate::prolog::machine::machine_errors::*;
use crate::prolog::machine::machine_indices::*;
use crate::prolog::machine::machine_state::*;
use crate::prolog::machine::streams::*;
use crate::prolog::machine::toplevel::to_op_decl;
use crate::prolog::ordered_float::OrderedFloat;
use crate::prolog::read::readline;
use crate::prolog::rug::Integer;

use crate::indexmap::IndexSet;

use crate::ref_thread_local::RefThreadLocal;

use std::cmp;
use std::collections::BTreeSet;
use std::convert::TryFrom;
use std::io::{ErrorKind, Read, Write};
use std::iter::{once, FromIterator};
use std::fs::{File, OpenOptions};
use std::net::{TcpListener, TcpStream};
use std::ops::Sub;
use std::rc::Rc;
use std::num::NonZeroU32;

use std::time::Duration;
use cpu_time::ProcessTime;

use crate::crossterm::event::{read, Event, KeyCode, KeyEvent, KeyModifiers};
use crate::crossterm::terminal::{enable_raw_mode, disable_raw_mode};

use ring::rand::{SecureRandom, SystemRandom};
use ring::{digest,hkdf,pbkdf2,aead,signature};
use ripemd160::{Ripemd160, Digest};
use sha3::{Sha3_224, Sha3_256, Sha3_384, Sha3_512};
use blake2::{Blake2s, Blake2b};

pub fn get_key() -> KeyEvent {
    let key;
    enable_raw_mode().expect("failed to enable raw mode");
    loop {
        let key_ = read();
        if let Ok(key_) = key_ {
            if let Event::Key(key_) = key_ {
                match key_.code {
                    KeyCode::Char(_) | KeyCode::Enter | KeyCode::Tab => {
                        key = key_;
                        break;
                    },
                    _ => ()
                }
            }
        }
    }
    disable_raw_mode().expect("failed to disable raw mode");
    key
}

#[derive(Debug)]
struct BrentAlgState {
    hare: Addr,
    tortoise: Addr,
    power: usize,
    steps: usize,
}

impl BrentAlgState {
    fn new(hare: Addr) -> Self {
        BrentAlgState {
            hare: hare,
            tortoise: hare,
            power: 2,
            steps: 0,
        }
    }

    #[inline]
    fn conclude_or_move_tortoise(&mut self) -> Option<CycleSearchResult> {
        if self.tortoise == self.hare {
            return Some(CycleSearchResult::NotList);
        } else if self.steps == self.power {
            self.tortoise = self.hare;
            self.power <<= 1;
        }

        None
    }

    #[inline]
    fn step(&mut self, hare: Addr) -> Option<CycleSearchResult> {
        self.hare = hare;
        self.steps += 1;

        self.conclude_or_move_tortoise()
    }

    fn to_result(self) -> CycleSearchResult {
        match self.hare {
            addr @ Addr::HeapCell(_) | addr @ Addr::StackCell(..) | addr @ Addr::AttrVar(_) => {
                CycleSearchResult::PartialList(self.steps, addr.as_var().unwrap())
            }
            Addr::PStrLocation(h, n) => {
                CycleSearchResult::PStrLocation(self.steps, h, n)
            }
            Addr::EmptyList => {
                CycleSearchResult::ProperList(self.steps)
            }
            _ => {
                CycleSearchResult::NotList
            }
        }
    }
}

fn is_builtin_predicate(name: &ClauseName) -> bool {
    let in_builtins = name.owning_module().as_str() == "builtins";
    let hidden_name = name.as_str().starts_with("$");

    in_builtins || hidden_name
}

impl MachineState {
    // a step in Brent's algorithm.
    fn brents_alg_step(&self, brent_st: &mut BrentAlgState) -> Option<CycleSearchResult> {
        match self.store(self.deref(brent_st.hare)) {
            Addr::EmptyList => {
                Some(CycleSearchResult::ProperList(brent_st.steps))
            }
            addr @ Addr::HeapCell(_) | addr @ Addr::StackCell(..) | addr @ Addr::AttrVar(_) => {
                Some(CycleSearchResult::PartialList(
                    brent_st.steps,
                    addr.as_var().unwrap(),
                ))
            }
            Addr::PStrLocation(h, n) => {
                match &self.heap[h] {
                    HeapCellValue::PartialString(ref pstr, _) => {
                        if let Some(c) = pstr.range_from(n ..).next() {
                            brent_st.step(Addr::PStrLocation(h, n + c.len_utf8()))
                        } else {
                            unreachable!()
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                }
            }
            Addr::Lis(l) => {
                brent_st.step(Addr::HeapCell(l + 1))
            }
            _ => {
                Some(CycleSearchResult::NotList)
            }
        }
    }

    pub(super)
    fn detect_cycles_with_max(&self, max_steps: usize, addr: Addr) -> CycleSearchResult {
        let hare = match self.store(self.deref(addr)) {
            Addr::Lis(offset) if max_steps > 0 => {
                Addr::Lis(offset)
            }
            Addr::Lis(offset) => {
                return CycleSearchResult::UntouchedList(offset);
            }
            Addr::PStrLocation(h, n) if max_steps > 0 => {
                Addr::PStrLocation(h, n)
            }
            Addr::PStrLocation(h, _) => {
                return CycleSearchResult::UntouchedList(h);
            }
            Addr::EmptyList => {
                return CycleSearchResult::EmptyList;
            }
            Addr::Con(h) if max_steps > 0 => {
                if let HeapCellValue::PartialString(..) = &self.heap[h] {
                    if !self.flags.double_quotes.is_atom() {
                        Addr::PStrLocation(h, 0)
                    } else {
                        return CycleSearchResult::NotList;
                    }
                } else {
                    return CycleSearchResult::NotList;
                }
            }
            Addr::Con(h) => {
                if let HeapCellValue::PartialString(..) = &self.heap[h] {
                    if !self.flags.double_quotes.is_atom() {
                        return CycleSearchResult::UntouchedList(h);
                    }
                }

                return CycleSearchResult::NotList;
            }
            _ => {
                return CycleSearchResult::NotList;
            }
        };

        let mut brent_st = BrentAlgState::new(hare);

        loop {
            if brent_st.steps == max_steps {
                return brent_st.to_result();
            }

            if let Some(result) = self.brents_alg_step(&mut brent_st) {
                return result;
            }
        }
    }

    pub(super)
    fn detect_cycles(&self, addr: Addr) -> CycleSearchResult {
        let addr = self.store(self.deref(addr));
        let hare = match addr {
            Addr::Lis(offset) => {
                Addr::Lis(offset)
            }
            Addr::EmptyList => {
                return CycleSearchResult::EmptyList;
            }
            Addr::PStrLocation(h, n) => {
                Addr::PStrLocation(h, n)
            }
            Addr::Con(h) => {
                if let HeapCellValue::PartialString(..) = &self.heap[h] {
                    if !self.flags.double_quotes.is_atom() {
                        Addr::PStrLocation(h, 0)
                    } else {
                        return CycleSearchResult::NotList;
                    }
                } else {
                    return CycleSearchResult::NotList;
                }
            }
            _ => {
                return CycleSearchResult::NotList;
            }
        };

        let mut brent_st = BrentAlgState::new(hare);

        loop {
            if let Some(result) = self.brents_alg_step(&mut brent_st) {
                return result;
            }
        }
    }

    fn finalize_skip_max_list(&mut self, n: usize, addr: Addr) {
        let target_n = self[temp_v!(1)];
        self.unify(Addr::Usize(n), target_n);

        if !self.fail {
            let xs = self[temp_v!(4)];
            self.unify(addr, xs);
        }
    }

    fn skip_max_list_result(&mut self, max_steps: Option<isize>) {
        let search_result =
            if let Some(max_steps) = max_steps {
                if max_steps == -1 {
                    self.detect_cycles(self[temp_v!(3)])
                } else {
                    self.detect_cycles_with_max(
                        max_steps as usize,
                        self[temp_v!(3)],
                    )
                }
            } else {
                self.detect_cycles(self[temp_v!(3)])
            };

        match search_result {
            CycleSearchResult::PStrLocation(steps, h, n) => {
                self.finalize_skip_max_list(steps, Addr::PStrLocation(h, n));
            }
            CycleSearchResult::UntouchedList(l) => {
                self.finalize_skip_max_list(0, Addr::Lis(l))
            }
            CycleSearchResult::EmptyList => {
                self.finalize_skip_max_list(0, Addr::EmptyList)
            }
            CycleSearchResult::PartialList(n, r) => {
                self.finalize_skip_max_list(n, r.as_addr())
            }
            CycleSearchResult::ProperList(steps) => {
                self.finalize_skip_max_list(steps, Addr::EmptyList)
            }
            CycleSearchResult::NotList => {
                let xs0 = self[temp_v!(3)];
                self.finalize_skip_max_list(0, xs0);
            }
        };
    }

    pub(super)
    fn skip_max_list(&mut self) -> CallResult {
        let max_steps = self.store(self.deref(self[temp_v!(2)]));

        match max_steps {
            Addr::HeapCell(_) | Addr::StackCell(..) | Addr::AttrVar(_) => {
                let stub = MachineError::functor_stub(clause_name!("$skip_max_list"), 4);
                return Err(self.error_form(MachineError::instantiation_error(), stub));
            }
            addr => {
                let max_steps_n =
                    match Number::try_from((max_steps, &self.heap)) {
                        Ok(Number::Integer(n)) => n.to_isize(),
                        Ok(Number::Fixnum(n))  => Some(n),
                        _ => None,
                    };

                if max_steps_n.map(|i| i >= -1).unwrap_or(false) {
                    let n = self.store(self.deref(self[temp_v!(1)]));

                    match Number::try_from((n, &self.heap)) {
                        Ok(Number::Integer(n)) => {
                            if n.as_ref() == &0 {
                                let xs0 = self[temp_v!(3)];
                                let xs  = self[temp_v!(4)];

                                self.unify(xs0, xs);
                            } else {
                                self.skip_max_list_result(max_steps_n);
                            }
                        }
                        Ok(Number::Fixnum(n)) => {
                            if n == 0 {
                                let xs0 = self[temp_v!(3)];
                                let xs  = self[temp_v!(4)];

                                self.unify(xs0, xs);
                            } else {
                                self.skip_max_list_result(max_steps_n);
                            }
                        }
                        _ => {
                            self.skip_max_list_result(max_steps_n);
                        }
                    }
                } else {
                    let stub = MachineError::functor_stub(clause_name!("$skip_max_list"), 4);
                    return Err(
                        self.error_form(
                            MachineError::type_error(
                                self.heap.h(),
                                ValidType::Integer,
                                addr
                            ),
                            stub,
                        )
                    );
                }
            }
        }

        Ok(())
    }

    #[inline]
    fn install_new_block(&mut self, r: RegType) -> usize {
        self.block = self.b;

        let c = Constant::Usize(self.block);
        let addr = self[r];

        self.write_constant_to_var(addr, &c);
        self.block
    }

    fn copy_findall_solution(&mut self, lh_offset: usize, copy_target: Addr) -> usize {
        let threshold = self.lifted_heap.h() - lh_offset;

        let mut copy_ball_term = CopyBallTerm::new(
            &mut self.stack,
            &mut self.heap,
            &mut self.lifted_heap,
        );

        copy_ball_term.push(HeapCellValue::Addr(Addr::Lis(threshold + 1)));
        copy_ball_term.push(HeapCellValue::Addr(Addr::HeapCell(threshold + 3)));
        copy_ball_term.push(HeapCellValue::Addr(Addr::HeapCell(threshold + 2)));

        copy_term(copy_ball_term, copy_target, AttrVarPolicy::DeepCopy);

        threshold + lh_offset + 2
    }

    fn repl_redirect(&mut self, repl_code_ptr: REPLCodePtr) -> CallResult {
        let p = if self.last_call {
            self.cp
        } else {
            self.p.local() + 1
        };

        Ok(self.p = CodePtr::REPL(repl_code_ptr, p))
    }

    fn truncate_if_no_lifted_heap_diff<AddrConstr>(&mut self, addr_constr: AddrConstr)
    where
        AddrConstr: Fn(usize) -> Addr,
    {
        match self.store(self.deref(self[temp_v!(1)])) {
            Addr::Usize(lh_offset) => {
                if lh_offset >= self.lifted_heap.h() {
                    self.lifted_heap.truncate(lh_offset);
                } else {
                    let threshold = self.lifted_heap.h() - lh_offset;
                    self.lifted_heap.push(HeapCellValue::Addr(addr_constr(threshold)));
                }
            }
            _ => self.fail = true,
        }
    }

    fn get_next_db_ref(&mut self, indices: &IndexStore, db_ref: &DBRef) {
        match db_ref {
            &DBRef::NamedPred(ref name, arity, _) => {
                let key = (name.clone(), arity);
                let mut iter = indices.code_dir.range(key..).skip(1);

                while let Some(((name, arity), idx)) = iter.next() {
                    if idx.is_undefined() {
                        self.fail = true;
                        return;
                    }

                    if is_builtin_predicate(&name) {
                        continue;
                    }

                    let a2 = self[temp_v!(2)];

                    if let Some(r) = a2.as_var() {
                        let spec = get_clause_spec(
                            name.clone(),
                            *arity,
                            composite_op!(&indices.op_dir),
                        );

                        let addr = self.heap.to_unifiable(HeapCellValue::DBRef(
                            DBRef::NamedPred(
                                name.clone(),
                                *arity,
                                spec,
                            )
                        ));

                        self.bind(r, addr);

                        return;
                    }
                }

                self.fail = true;
            }
            &DBRef::Op(_, spec, ref name, ref op_dir, _) => {
                let fixity = match spec {
                    XF | YF => Fixity::Post,
                    FX | FY => Fixity::Pre,
                    _ => Fixity::In,
                };

                let key = OrderedOpDirKey(name.clone(), fixity);

                match op_dir.range(key..).skip(1).next() {
                    Some((OrderedOpDirKey(name, _), (priority, spec))) => {
                        let a2 = self[temp_v!(2)];

                        if let Some(r) = a2.as_var() {
                            let addr = self.heap.to_unifiable(
                                HeapCellValue::DBRef(
                                    DBRef::Op(
                                        *priority,
                                        *spec,
                                        name.clone(),
                                        op_dir.clone(),
                                        SharedOpDesc::new(*priority, *spec)
                                    ),
                                ),
                            );

                            self.bind(r, addr);
                        } else {
                            self.fail = true;
                        }
                    }
                    None => self.fail = true,
                }
            }
        }
    }

    fn int_to_char(
        &self,
        n: &Integer,
        stub: &'static str,
        arity: usize,
    ) -> Result<char, MachineStub>
    {
        let c = n.to_u32().and_then(std::char::from_u32);

        if let Some(c) = c {
            Ok(c)
        } else {
            let stub = MachineError::functor_stub(clause_name!(stub), arity);
            let err = MachineError::representation_error(RepFlag::CharacterCode);
            let err = self.error_form(err, stub);

            Err(err)
        }
    }

    fn parse_number_from_string(
        &mut self,
        mut string: String,
        indices: &IndexStore,
        stub: MachineStub,
    ) -> CallResult {
        let nx = self[temp_v!(2)];

        if let Some(c) = string.chars().last() {
            if layout_char!(c) {
                let (line_num, col_num) = string.chars().fold((0, 0), |(line_num, col_num), c| {
                    if new_line_char!(c) {
                        (1 + line_num, 0)
                    } else {
                        (line_num, col_num + 1)
                    }
                });
                let err = ParserError::UnexpectedChar(c, line_num, col_num);

                let h = self.heap.h();
                let err = MachineError::syntax_error(h, err);

                return Err(self.error_form(err, stub));
            }
        }

        string.push('.');

        let mut stream =
            match parsing_stream(std::io::Cursor::new(string)) {
                Ok(stream) => {
                    stream
                }
                Err(e) => {
                    let err = MachineError::session_error(
                        self.heap.h(),
                        SessionError::from(e),
                    );

                    return Err(self.error_form(err, stub));
                }
            };

        let mut parser = Parser::new(
            &mut stream,
            indices.atom_tbl.clone(),
            self.machine_flags(),
        );

        match parser.read_term(composite_op!(&indices.op_dir)) {
            Err(err) => {
                let h = self.heap.h();
                let err = MachineError::syntax_error(h, err);

                return Err(self.error_form(err, stub));
            }
            Ok(Term::Constant(_, Constant::Rational(n))) => {
                let addr = self.heap.put_constant(Constant::Rational(n));
                self.unify(nx, addr);
            }
            Ok(Term::Constant(_, Constant::Float(n))) => {
                let addr = self.heap.put_constant(Constant::Float(n));
                self.unify(nx, addr);
            }
            Ok(Term::Constant(_, Constant::Integer(n))) => {
                let addr = self.heap.put_constant(Constant::Integer(n));
                self.unify(nx, addr);
            }
            Ok(Term::Constant(_, Constant::Fixnum(n))) => {
                let addr = self.heap.put_constant(Constant::Fixnum(n));
                self.unify(nx, addr);
            }
            _ => {
                let err = ParserError::ParseBigInt(0, 0);

                let h = self.heap.h();
                let err = MachineError::syntax_error(h, err);

                return Err(self.error_form(err, stub));
            }
        }

        Ok(())
    }

    fn fetch_attribute_goals(&mut self, mut attr_goals: Vec<Addr>) {
        attr_goals.sort_unstable_by(|a1, a2| {
            self.compare_term_test(a1, a2)
                .unwrap_or(cmp::Ordering::Less)
        });

        self.term_dedup(&mut attr_goals);

        let attr_goals = Addr::HeapCell(self.heap.to_list(attr_goals.into_iter()));
        let target = self[temp_v!(1)];

        self.unify(attr_goals, target);
    }

    fn call_continuation_chunk(&mut self, chunk: Addr, return_p: LocalCodePtr) -> LocalCodePtr {
        let chunk = self.store(self.deref(chunk));

        match chunk {
            Addr::Str(s) => {
                match &self.heap[s] {
                    HeapCellValue::NamedStr(arity, ..) => {
                        let num_cells = arity - 1;
                        let p_functor = self.heap[s+1].as_addr(s+1);

                        let cp = self.heap.to_local_code_ptr(&p_functor).unwrap();
                        let prev_e = self.e;

                        let e = self.stack.allocate_and_frame(num_cells);
                        let and_frame = self.stack.index_and_frame_mut(e);

                        and_frame.prelude.e  = prev_e;
                        and_frame.prelude.cp = return_p;

                        self.p = CodePtr::Local(cp + 1);

                        // adjust cut point to occur after call_continuation.
                        if num_cells > 0 {
                            if let Addr::CutPoint(_) = self.heap[s+2].as_addr(s+2) {
                                and_frame[1] = Addr::CutPoint(self.b);
                            } else {
                                and_frame[1] = self.heap[s+2].as_addr(s+2);
                            }
                        }

                        for index in s+3 .. s+2+num_cells {
                            and_frame[index - (s+1)] = self.heap[index].as_addr(index);
                        }

                        self.e = e;

                        self.p.local()
                    }
                    _ => unreachable!()
                }
            }
            _ => unreachable!()
        }
    }

    pub(super)
    fn system_call(
        &mut self,
        ct: &SystemClauseType,
        code_repo: &CodeRepo,
        indices: &mut IndexStore,
        call_policy: &mut Box<dyn CallPolicy>,
        cut_policy: &mut Box<dyn CutPolicy>,
        current_input_stream: &mut Stream,
        current_output_stream: &mut Stream,
    ) -> CallResult {
        match ct {
            &SystemClauseType::AbolishClause => {
                let p = self.cp;
                let trans_type = DynamicTransactionType::Abolish;

                self.p = CodePtr::DynamicTransaction(trans_type, p);
                return Ok(());
            }
            &SystemClauseType::AbolishModuleClause => {
                let p = self.cp;
                let trans_type = DynamicTransactionType::ModuleAbolish;

                self.p = CodePtr::DynamicTransaction(trans_type, p);
                return Ok(());
            }
            &SystemClauseType::BindFromRegister => {
                let reg = self.store(self.deref(self[temp_v!(2)]));
                let n =
                    match Number::try_from((reg, &self.heap)) {
                        Ok(Number::Integer(n)) => {
                            n.to_usize()
                        }
                        Ok(Number::Fixnum(n)) => {
                            usize::try_from(n).ok()
                        }
                        _ => {
                            unreachable!()
                        }
                    };

                if let Some(n) = n {
                    if n <= MAX_ARITY {
                        let target = self[temp_v!(n)];
                        let addr   = self[temp_v!(1)];

                        self.unify(addr, target);
                        return return_from_clause!(self.last_call, self);
                    }
                }

                self.fail = true;
            }
            &SystemClauseType::AssertDynamicPredicateToFront => {
                let p = self.cp;
                let trans_type = DynamicTransactionType::Assert(DynamicAssertPlace::Front);

                self.p = CodePtr::DynamicTransaction(trans_type, p);
                return Ok(());
            }
            &SystemClauseType::AssertDynamicPredicateToBack => {
                let p = self.cp;
                let trans_type = DynamicTransactionType::Assert(DynamicAssertPlace::Back);

                self.p = CodePtr::DynamicTransaction(trans_type, p);
                return Ok(());
            }
            &SystemClauseType::CurrentHostname => {
                match hostname::get().ok() {
                    Some(host) => {
                        match host.into_string().ok() {
                            Some(host) => {
                                let hostname = self.heap.to_unifiable(
                                    HeapCellValue::Atom(clause_name!(host, indices.atom_tbl), None)
                                );

                                self.unify(self[temp_v!(1)], hostname);
                                return return_from_clause!(self.last_call, self);
                            }
                            None => {
                            }
                        }
                    }
                    None => {
                    }
                }

                self.fail = true;
                return Ok(());
            }
            &SystemClauseType::CurrentInput => {
                let addr = self.store(self.deref(self[temp_v!(1)]));

                let stream = current_input_stream.clone();

                match addr {
                    addr if addr.is_ref() => {
                        let stream = self.heap.to_unifiable(HeapCellValue::Stream(stream));
                        self.unify(stream, addr);
                    }
                    Addr::Stream(other_stream) => {
                        if let HeapCellValue::Stream(ref other_stream) = &self.heap[other_stream] {
                            self.fail = current_input_stream != other_stream;
                        } else {
                            unreachable!()
                        }
                    }
                    addr => {
                        let stub = MachineError::functor_stub(
                            clause_name!("current_input"),
                            1,
                        );

                        let err = MachineError::domain_error(
                            DomainErrorType::Stream,
                            addr,
                        );

                        return Err(self.error_form(err, stub));
                    }
                }
            }
            &SystemClauseType::CurrentOutput => {
                let addr = self.store(self.deref(self[temp_v!(1)]));
                let stream = current_output_stream.clone();

                match addr {
                    addr if addr.is_ref() => {
                        let stream = self.heap.to_unifiable(HeapCellValue::Stream(stream));
                        self.unify(stream, addr);
                    }
                    Addr::Stream(other_stream) => {
                        if let HeapCellValue::Stream(ref other_stream) = &self.heap[other_stream] {
                            self.fail = current_output_stream != other_stream;
                        } else {
                            unreachable!()
                        }
                    }
                    addr => {
                        let stub = MachineError::functor_stub(
                            clause_name!("current_input"),
                            1,
                        );

                        let err = MachineError::domain_error(
                            DomainErrorType::Stream,
                            addr,
                        );

                        return Err(self.error_form(err, stub));
                    }
                }
            }
            &SystemClauseType::AtEndOfExpansion => {
                if self.cp == LocalCodePtr::TopLevel(0, 0) {
                    self.at_end_of_expansion = true;
                }
            }
            &SystemClauseType::AtomChars => {
                let a1 = self[temp_v!(1)];

                match self.store(self.deref(a1)) {
                    Addr::Char(c) => {
                        let iter = once(Addr::Char(c));
                        let list_of_chars = Addr::HeapCell(self.heap.to_list(iter));

                        let a2 = self[temp_v!(2)];
                        self.unify(a2, list_of_chars);
                    }
                    Addr::Con(h) if self.heap.atom_at(h) => {
	                    if let HeapCellValue::Atom(name, _) = self.heap.clone(h) {
                            let iter = name.as_str().chars().map(|c| Addr::Char(c));
                            let list_of_chars = Addr::HeapCell(self.heap.to_list(iter));

                            let a2 = self[temp_v!(2)];

                            match self.store(self.deref(a2)) {
                                Addr::PStrLocation(..)
                                    if !self.flags.double_quotes.is_chars() => {
                                        self.fail = true;
                                    }
                                a2 => {
                                    self.unify(a2, list_of_chars);
                                }
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    Addr::EmptyList => {
                        let a2 = self[temp_v!(2)];
                        let chars = vec![
                            Addr::Char('['),
                            Addr::Char(']'),
                        ];

                        let list_of_chars =
                            Addr::HeapCell(self.heap.to_list(chars.into_iter()));

                        self.unify(a2, list_of_chars);
                    }
                    addr if addr.is_ref() => {
                        let mut iter = self.heap_pstr_iter(self[temp_v!(2)]);
                        let string = iter.to_string();

                        match iter.focus() {
                            Addr::EmptyList => {
                                let chars = clause_name!(string, indices.atom_tbl);
                                let atom  = self.heap.to_unifiable(
                                    HeapCellValue::Atom(chars, None)
                                );

                                self.unify(addr, atom);
                            }
                            focus => {
                                let stub = MachineError::functor_stub(
                                    clause_name!("atom_chars"),
                                    2,
                                );

                                if let Addr::Lis(l) = focus {
                                    let err = MachineError::type_error(
                                        self.heap.h(),
                                        ValidType::Character,
                                        Addr::HeapCell(l),
                                    );

                                    return Err(self.error_form(err, stub));
                                } else {
                                    unreachable!()
                                }
                            }
                        }
                    }
                    _ => unreachable!(),
                };
            }
            &SystemClauseType::AtomCodes => {
                let a1 = self[temp_v!(1)];

                match self.store(self.deref(a1)) {
                    Addr::Char(c) => {
                        let iter = once(Addr::Fixnum(c as isize));
                        let list_of_codes = Addr::HeapCell(self.heap.to_list(iter));

                        let a2 = self[temp_v!(2)];
                        self.unify(a2, list_of_codes);
                    }
                    Addr::Con(h) if self.heap.atom_at(h) => {
	                if let HeapCellValue::Atom(name, _) = self.heap.clone(h) {
                            let a2 = self[temp_v!(2)];

                            match self.store(self.deref(a2)) {
                                a2 @ Addr::PStrLocation(..) => {
                                    if !self.flags.double_quotes.is_codes() {
                                        self.fail = true;
                                    } else {
                                        let iter = name
                                            .as_str()
                                            .chars()
                                            .map(|c| Addr::Char(c));

                                        let list_of_codes = Addr::HeapCell(self.heap.to_list(iter));

                                        self.unify(a2, list_of_codes);
                                    }
                                }
                                a2 => {
                                    let iter = name
                                        .as_str()
                                        .chars()
                                        .map(|c| Addr::Fixnum(c as isize));

                                    let list_of_codes = Addr::HeapCell(self.heap.to_list(iter));

                                    self.unify(a2, list_of_codes);
                                }
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    Addr::EmptyList => {
                        let chars = vec![
                            Addr::Fixnum('[' as isize),
                            Addr::Fixnum(']' as isize),
                        ];

                        let list_of_codes = Addr::HeapCell(self.heap.to_list(chars.into_iter()));
                        let a2 = self[temp_v!(2)];

                        self.unify(a2, list_of_codes);
                    }
                    addr if addr.is_ref() => {
                        let stub = MachineError::functor_stub(clause_name!("atom_codes"), 2);

                        match self.try_from_list(temp_v!(2), stub) {
                            Err(e) => return Err(e),
                            Ok(addrs) => {
                                let mut chars = String::new();

                                for addr in addrs {
                                    let addr = self.store(self.deref(addr));

                                    match Number::try_from((addr, &self.heap)) {
                                        Ok(Number::Fixnum(n)) => {
                                            let c = self.int_to_char(
                                                &Integer::from(n),
                                                "atom_codes",
                                                2,
                                            )?;

                                            chars.push(c);
                                            continue;
                                        }
                                        Ok(Number::Integer(n)) => {
                                            let c = self.int_to_char(&n, "atom_codes", 2)?;
                                            chars.push(c);

                                            continue;
                                        }
                                        _ => {
                                            let stub = MachineError::functor_stub(
                                                clause_name!("atom_codes"),
                                                2,
                                            );

                                            let err = MachineError::type_error(
                                                self.heap.h(),
                                                ValidType::Integer,
                                                addr,
                                            );

                                            return Err(self.error_form(err, stub));
                                        }
                                    }
                                }

                                let string = self.heap.to_unifiable(
                                    HeapCellValue::Atom(clause_name!(chars, indices.atom_tbl), None)
                                );

                                self.bind(addr.as_var().unwrap(), string);
                            }
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                };
            }
            &SystemClauseType::AtomLength => {
                let a1 = self.store(self.deref(self[temp_v!(1)]));

                let atom = match self.store(self.deref(a1)) {
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(ref name, _) = &self.heap[h] {
                            name.clone()
                        } else {
                            unreachable!()
                        }
                    }
                    Addr::EmptyList => {
                        clause_name!("[]")
                    }
                    Addr::Char(c) => {
                        clause_name!(c.to_string(), indices.atom_tbl)
                    }
                    _ => {
                        unreachable!()
                    }
                };

                let len = Integer::from(atom.as_str().chars().count());
                let len = self.heap.to_unifiable(HeapCellValue::Integer(Rc::new(len)));

                let a2 = self[temp_v!(2)];

                self.unify(a2, len);
            }
            &SystemClauseType::CallContinuation => {
                let stub = MachineError::functor_stub(clause_name!("call_continuation"), 1);

                match self.try_from_list(temp_v!(1), stub) {
                    Err(e) => return Err(e),
                    Ok(cont_chunks) => {
                        let mut return_p = if self.last_call {
                            self.cp
                        } else {
                            self.p.local() + 1
                        };

                        self.p = CodePtr::Local(return_p);

                        for chunk in cont_chunks.into_iter().rev() {
                            return_p = self.call_continuation_chunk(chunk, return_p);
                        }
                    }
                }

                return Ok(());
            }
            &SystemClauseType::CharsToNumber => {
                let stub = MachineError::functor_stub(clause_name!("number_chars"), 2);

                match self.try_from_list(temp_v!(1), stub) {
                    Err(e) => {
                        return Err(e);
                    }
                    Ok(addrs) => {
                        match self.try_char_list(addrs) {
                            Ok(string) => {
                                let stub = MachineError::functor_stub(clause_name!("number_chars"), 2);
                                self.parse_number_from_string(string, indices, stub)?;
                            }
                            Err(err) => {
                                let stub = MachineError::functor_stub(
                                    clause_name!("number_chars"),
                                    2,
                                );

                                return Err(self.error_form(err, stub));
                            }
                        }
                    }
                }
            }
            &SystemClauseType::CreatePartialString => {
                let atom = match self.store(self.deref(self[temp_v!(1)])) {
                    Addr::Con(h) => {
                        if let HeapCellValue::Atom(ref name, _) = &self.heap[h] {
                            name.clone()
                        } else {
                            unreachable!()
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                };

                let h = self.heap.h();

                if atom.as_str().is_empty() {
                    self.fail = true;
                    return Ok(());
                }

                let pstr = self.heap.allocate_pstr(atom.as_str());
                let pstr_tail = self.heap[h + 1].as_addr(h + 1);

                self.unify(self[temp_v!(2)], pstr);

                if !self.fail {
                    self.unify(self[temp_v!(3)], pstr_tail);
                }
            }
            &SystemClauseType::IsPartialString => {
                let addr = self.store(self.deref(self[temp_v!(1)]));

                match addr {
                    Addr::EmptyList => {
                        return return_from_clause!(self.last_call, self);
                    }
                    Addr::AttrVar(_) | Addr::HeapCell(_) | Addr::StackCell(..) => {
                        self.fail = true;
                        return Ok(());
                    }
                    _ => {
                    }
                }

                let mut heap_pstr_iter = self.heap_pstr_iter(addr);

                while let Some(_) = heap_pstr_iter.next() {}

                self.fail =
                    match heap_pstr_iter.focus() {
                        Addr::AttrVar(_) | Addr::HeapCell(_) | Addr::StackCell(..) |
                        Addr::EmptyList => {
                            false
                        }
                        _ => {
                            true
                        }
                    };
            }
            &SystemClauseType::PartialStringTail => {
                let pstr = self.store(self.deref(self[temp_v!(1)]));

                match pstr {
                    Addr::PStrLocation(h, _) => {
                        if let HeapCellValue::PartialString(_, true) = &self.heap[h] {
                            let tail = self.heap[h + 1].as_addr(h + 1);
                            let target = self[temp_v!(2)];

                            self.unify(tail, target);
                        } else {
                            self.fail = true;
                            return Ok(());
                        }
                    }
                    Addr::Lis(h) => {
                        self.unify(Addr::HeapCell(h + 1), self[temp_v!(2)]);
                    }
                    Addr::EmptyList => {
                        self.fail = true;
                        return Ok(());
                    }
                    _ => {
                        unreachable!()
                    }
                }
            }
            &SystemClauseType::PeekByte => {
                let mut stream =
                    self.get_stream_or_alias(self[temp_v!(1)], indices, "peek_byte", 2)?;

                self.check_stream_properties(
                    &mut stream,
                    StreamType::Binary,
                    Some(self[temp_v!(2)]),
                    clause_name!("peek_byte"),
                    2,
                )?;

                if stream.past_end_of_stream() {
                    if EOFAction::Reset != stream.options.eof_action {
                        return return_from_clause!(self.last_call, self);
                    } else if self.fail {
                        return Ok(());
                    }
                }

                if stream.at_end_of_stream() {
                    stream.set_past_end_of_stream();
                    self.unify(self[temp_v!(2)], Addr::Fixnum(-1));
                    return return_from_clause!(self.last_call, self);
                }

                let addr =
                    match self.store(self.deref(self[temp_v!(2)])) {
                        addr if addr.is_ref() => {
                            addr
                        }
                        addr => {
                            match Number::try_from((addr, &self.heap)) {
                                Ok(Number::Integer(n)) => {
                                    if let Some(nb) = n.to_u8() {
                                        Addr::Usize(nb as usize)
                                    } else {
                                        return Err(self.type_error(
                                            ValidType::InByte,
                                            addr,
                                            clause_name!("peek_byte"),
                                            2,
                                        ));
                                    }
                                }
                                Ok(Number::Fixnum(n)) => {
                                    if let Ok(nb) = u8::try_from(n) {
                                        Addr::Usize(nb as usize)
                                    } else {
                                        return Err(self.type_error(
                                            ValidType::InByte,
                                            addr,
                                            clause_name!("peek_byte"),
                                            2,
                                        ));
                                    }
                                }
                                _ => {
                                    return Err(self.type_error(
                                        ValidType::InByte,
                                        addr,
                                        clause_name!("peek_byte"),
                                        2,
                                    ));
                                }
                            }
                        }
                    };

                loop {
                    match stream.peek_byte().map_err(|e| e.kind()) {
                        Ok(b) => {
                            if let Some(var) = addr.as_var() {
                                self.bind(var, Addr::Usize(b as usize));
                                break;
                            } else if addr == Addr::Usize(b as usize) {
                                break;
                            } else {
                                self.fail = true;
                                return Ok(());
                            }
                        }
                        Err(ErrorKind::PermissionDenied) => {
                            self.fail = true;
                            break;
                        }
                        _ => {
                            self.eof_action(
                                self[temp_v!(2)],
                                &mut stream,
                                clause_name!("peek_byte"),
                                2,
                            )?;

                            if EOFAction::Reset != stream.options.eof_action {
                                return return_from_clause!(self.last_call, self);
                            } else if self.fail {
                                return Ok(());
                            }
                        }
                    }
                }
            }
            &SystemClauseType::PeekChar => {
                let mut stream =
                    self.get_stream_or_alias(self[temp_v!(1)], indices, "peek_char", 2)?;

                self.check_stream_properties(
                    &mut stream,
                    StreamType::Text,
                    Some(self[temp_v!(2)]),
                    clause_name!("peek_char"),
                    2,
                )?;

                if stream.past_end_of_stream() {
                    if EOFAction::Reset != stream.options.eof_action {
                        return return_from_clause!(self.last_call, self);
                    } else if self.fail {
                        return Ok(());
                    }
                }

                if stream.at_end_of_stream() {
                    let end_of_file = clause_name!("end_of_file");
                    let end_of_file = self.heap.to_unifiable(
                        HeapCellValue::Atom(end_of_file, None),
                    );

                    stream.set_past_end_of_stream();

                    self.unify(self[temp_v!(2)], end_of_file);
                    return return_from_clause!(self.last_call, self);
                }

                let addr =
                    match self.store(self.deref(self[temp_v!(2)])) {
                        addr if addr.is_ref() => {
                            addr
                        }
                        Addr::Con(h) if self.heap.atom_at(h) => {
                            match &self.heap[h] {
                                HeapCellValue::Atom(ref atom, _) if atom.is_char() => {
                                    if let Some(c) = atom.as_str().chars().next() {
                                        Addr::Char(c)
                                    } else {
                                        unreachable!()
                                    }
                                }
                                culprit => {
                                    return Err(self.type_error(
                                        ValidType::InCharacter,
                                        culprit.as_addr(h),
                                        clause_name!("peek_char"),
                                        2,
                                    ));
                                }
                            }
                        }
                        Addr::Char(d) => {
                            Addr::Char(d)
                        }
                        culprit => {
                            return Err(self.type_error(
                                ValidType::InCharacter,
                                culprit,
                                clause_name!("peek_char"),
                                2,
                            ));
                        }
                    };

                loop {
                    match stream.peek_char().map_err(|e| e.kind()) {
                        Ok(d) => {
                            if let Some(var) = addr.as_var() {
                                self.bind(var, Addr::Char(d));
                                break;
                            } else if addr == Addr::Char(d) {
                                break;
                            } else {
                                self.fail = true;
                                return Ok(());
                            }
                        }
                        Err(ErrorKind::PermissionDenied) => {
                            self.fail = true;
                            break;
                        }
                        _ => {
                            self.eof_action(
                                self[temp_v!(2)],
                                &mut stream,
                                clause_name!("peek_char"),
                                2,
                            )?;

                            if EOFAction::Reset != stream.options.eof_action {
                                return return_from_clause!(self.last_call, self);
                            } else if self.fail {
                                return Ok(());
                            }
                        }/*
                        _ => {
                            let stub = MachineError::functor_stub(clause_name!("peek_char"), 2);
                            let err = MachineError::representation_error(RepFlag::Character);
                            let err = self.error_form(err, stub);

                            return Err(err);
                        }*/
                    }
                }
            }
            &SystemClauseType::PeekCode => {
                let mut stream =
                    self.get_stream_or_alias(self[temp_v!(1)], indices, "peek_code", 2)?;

                self.check_stream_properties(
                    &mut stream,
                    StreamType::Text,
                    Some(self[temp_v!(2)]),
                    clause_name!("peek_code"),
                    2,
                )?;

                if stream.past_end_of_stream() {
                    if EOFAction::Reset != stream.options.eof_action {
                        return return_from_clause!(self.last_call, self);
                    } else if self.fail {
                        return Ok(());
                    }
                }

                if stream.at_end_of_stream() {
                    let end_of_file = clause_name!("end_of_file");
                    let end_of_file = self.heap.to_unifiable(
                        HeapCellValue::Atom(end_of_file, None),
                    );

                    stream.set_past_end_of_stream();

                    self.unify(self[temp_v!(2)], end_of_file);
                    return return_from_clause!(self.last_call, self);
                }

                let addr =
                    match self.store(self.deref(self[temp_v!(2)])) {
                        addr if addr.is_ref() => {
                            addr
                        }
                        addr => {
                            match Number::try_from((addr, &self.heap)) {
                                Ok(Number::Integer(n)) => {
                                    let n = n.to_u32().and_then(|n| {
                                        std::char::from_u32(n).and_then(|_| Some(n))
                                    });

                                    if let Some(n) = n {
                                        Addr::Fixnum(n as isize)
                                    } else {
                                        return Err(self.representation_error(
                                            RepFlag::InCharacterCode,
                                            clause_name!("peek_code"),
                                            2,
                                        ));
                                    }
                                }
                                Ok(Number::Fixnum(n)) => {
                                    let n = u32::try_from(n).ok().and_then(|n| {
                                        std::char::from_u32(n).and_then(|_| Some(n))
                                    });

                                    if let Some(n) = n {
                                        Addr::Fixnum(n as isize)
                                    } else {
                                        return Err(self.representation_error(
                                            RepFlag::InCharacterCode,
                                            clause_name!("peek_code"),
                                            2,
                                        ));
                                    }
                                }
                                _ => {
                                    return Err(self.type_error(
                                        ValidType::Integer,
                                        self[temp_v!(2)],
                                        clause_name!("peek_code"),
                                        2,
                                    ));
                                }
                            }
                        }
                    };

                loop {
                    let result = stream.peek_char();

                    match result.map_err(|e| e.kind()) {
                        Ok(c) => {
                            if let Some(var) = addr.as_var() {
                                self.bind(var, Addr::Fixnum(c as isize));
                                break;
                            } else if addr == Addr::Fixnum(c as isize) {
                                break;
                            } else {
                                self.fail = true;
                                return Ok(());
                            }
                        }
                        Err(ErrorKind::PermissionDenied) => {
                            self.fail = true;
                            break;
                        }
                        _ => {
                            self.eof_action(
                                self[temp_v!(2)],
                                &mut stream,
                                clause_name!("peek_code"),
                                2,
                            )?;

                            if EOFAction::Reset != stream.options.eof_action {
                                return return_from_clause!(self.last_call, self);
                            } else if self.fail {
                                return Ok(());
                            }
                        }/*
                        _ => {
                            let stub = MachineError::functor_stub(clause_name!("get_char"), 2);
                            let err = MachineError::representation_error(RepFlag::Character);
                            let err = self.error_form(err, stub);

                            return Err(err);
                        }*/
                    }
                }
            }
            &SystemClauseType::NumberToChars => {
                let n = self[temp_v!(1)];
                let chs = self[temp_v!(2)];

                let n = self.store(self.deref(n));

                let string =
                    match Number::try_from((n, &self.heap)) {
                        Ok(Number::Float(OrderedFloat(n))) => {
                            format!("{0:<20?}", n)
                        }
                        Ok(Number::Fixnum(n)) => {
                            n.to_string()
                        }
                        Ok(Number::Integer(n)) => {
                            n.to_string()
                        }
                        _ => {
                            unreachable!()
                        }
                    };

                let chars = string.trim().chars().map(|c| Addr::Char(c));
                let char_list = Addr::HeapCell(self.heap.to_list(chars));

                self.unify(char_list, chs);
            }
            &SystemClauseType::NumberToCodes => {
                let n = self[temp_v!(1)];
                let chs = self[temp_v!(2)];

                let string =
                    match Number::try_from((n, &self.heap)) {
                        Ok(Number::Float(OrderedFloat(n))) => {
                            format!("{0:<20?}", n)
                        }
                        Ok(Number::Fixnum(n)) => {
                            n.to_string()
                        }
                        Ok(Number::Integer(n)) => {
                            n.to_string()
                        }
                        _ => {
                            unreachable!()
                        }
                    };

                let codes = string
                    .trim()
                    .chars()
                    .map(|c| Addr::Fixnum(c as isize));

                let codes_list = Addr::HeapCell(self.heap.to_list(codes));

                self.unify(codes_list, chs);
            }
            &SystemClauseType::CodesToNumber => {
                let stub = MachineError::functor_stub(clause_name!("number_codes"), 2);

                match self.try_from_list(temp_v!(1), stub) {
                    Err(e) => {
                        return Err(e);
                    }
                    Ok(addrs) => {
                        match self.try_char_list(addrs) {
                            Ok(chars) => {
                                let stub = MachineError::functor_stub(clause_name!("number_codes"), 2);
                                self.parse_number_from_string(chars, indices, stub)?;
                            }
                            Err(err) => {
                                let stub = MachineError::functor_stub(
                                    clause_name!("number_codes"),
                                    2,
                                );

                                return Err(self.error_form(err, stub));
                            }
                        }
                    }
                }
            }
            &SystemClauseType::ModuleAssertDynamicPredicateToFront => {
                let p = self.cp;
                let trans_type = DynamicTransactionType::ModuleAssert(DynamicAssertPlace::Front);

                self.p = CodePtr::DynamicTransaction(trans_type, p);
                return Ok(());
            }
            &SystemClauseType::ModuleAssertDynamicPredicateToBack => {
                let p = self.cp;
                let trans_type = DynamicTransactionType::ModuleAssert(DynamicAssertPlace::Back);

                self.p = CodePtr::DynamicTransaction(trans_type, p);
                return Ok(());
            }
            &SystemClauseType::LiftedHeapLength => {
                let a1 = self[temp_v!(1)];
                let lh_len = Addr::Usize(self.lifted_heap.h());

                self.unify(a1, lh_len);
            }
            &SystemClauseType::CharCode => {
                let a1 = self[temp_v!(1)];

                match self.store(self.deref(a1)) {
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        let c =
                            if let HeapCellValue::Atom(name, _) = &self.heap[h] {
                                if name.is_char() {
                                    name.as_str().chars().next().unwrap()
                                } else {
                                    self.fail = true;
                                    return Ok(());
                                }
                            } else {
                                unreachable!()
                            };

                        let a2 = self[temp_v!(2)];
                        self.unify(Addr::Fixnum(c as isize), a2);
                    }
                    Addr::Char(c) => {
                        let a2 = self[temp_v!(2)];
                        self.unify(Addr::Fixnum(c as isize), a2);
                    }
                    addr if addr.is_ref() => {
                        let a2 = self[temp_v!(2)];
                        let a2 = self.store(self.deref(a2));

                        let c = match Number::try_from((a2, &self.heap)) {
                            Ok(Number::Integer(n)) => {
                                self.int_to_char(&n, "char_code", 2)?
                            }
                            Ok(Number::Fixnum(n)) => {
                                self.int_to_char(&Integer::from(n), "char_code", 2)?
                            }
                            _ => {
                                self.fail = true;
                                return Ok(());
                            }
                        };

                        self.unify(Addr::Char(c), addr);
                    }
                    _ => {
                        unreachable!();
                    }
                };
            }
            &SystemClauseType::CharType => {
                let a1 = self.store(self.deref(self[temp_v!(1)]));
                let a2 = self.store(self.deref(self[temp_v!(2)]));

                let c = match a1 {
                    Addr::Char(c) => c,
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(name, _) = &self.heap[h] {
                            name.as_str().chars().next().unwrap()
                        }
                        else {
                            unreachable!()
                        }
                    }
                    _ => unreachable!()
                };
                let chars = match a2 {
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(name, _) = &self.heap[h] {
                            name.as_str().to_string()
                        }
                        else {
                            unreachable!()
                        }
                    }
                    Addr::Char(c) => {
                        c.to_string()
                    }
                    _ => unreachable!()
                };
                self.fail = true; // This predicate fails by default.
                macro_rules! macro_check {
                    ($id:ident, $name:tt) => {
                if $id!(c) && chars == $name {
                    self.fail = false;

                    return return_from_clause!(self.last_call, self);
                }
                    }
                }
                macro_rules! method_check {
                    ($id:ident, $name:tt) => {
                if c.$id() && chars == $name {
                    self.fail = false;

                    return return_from_clause!(self.last_call, self);
                }
                    }
                }
                macro_check!(symbolic_control_char, "symbolic_control");
                // macro_check!(space_char, "space");
                macro_check!(layout_char, "layout");
                macro_check!(symbolic_hexadecimal_char, "symbolic_hexadecimal");
                macro_check!(octal_digit_char, "octal_digit");
                macro_check!(binary_digit_char, "binary_digit");
                macro_check!(hexadecimal_digit_char, "hexadecimal_digit");
                macro_check!(exponent_char, "exponent");
                macro_check!(sign_char, "sign");
                // macro_check!(new_line_char, "new_line");
                // macro_check!(comment_1_char, "comment_1");
                // macro_check!(comment_2_char, "comment_2");
                // macro_check!(capital_letter_char, "upper");
                // macro_check!(small_letter_char, "lower");
                // macro_check!(variable_indicator_char, "variable_indicator");
                macro_check!(graphic_char, "graphic");
                macro_check!(graphic_token_char, "graphic_token");
                macro_check!(alpha_char, "alpha");
                macro_check!(decimal_digit_char, "decimal_digit");
                // macro_check!(decimal_point_char, "decimal_point");
                // macro_check!(alpha_numeric_char, "alnum");
                // macro_check!(cut_char, "cut");
                // macro_check!(semicolon_char, "semicolon");
                // macro_check!(backslash_char, "backslash");
                // macro_check!(single_quote_char, "single_quote");
                // macro_check!(double_quote_char, "double_quote");
                // macro_check!(back_quote_char, "back_quote");
                macro_check!(meta_char, "meta");
                macro_check!(solo_char, "solo");
                macro_check!(prolog_char, "prolog");
                method_check!(is_alphabetic, "alphabetic");
                method_check!(is_lowercase, "lower");
                method_check!(is_uppercase, "upper");
                method_check!(is_whitespace, "whitespace");
                method_check!(is_alphanumeric, "alnum");
                method_check!(is_control, "control");
                method_check!(is_numeric, "numeric");
                method_check!(is_ascii, "ascii");
                method_check!(is_ascii_punctuation, "ascii_ponctuaction");
                method_check!(is_ascii_graphic, "ascii_graphic");
            }
            &SystemClauseType::CheckCutPoint => {
                let addr = self.store(self.deref(self[temp_v!(1)]));

                match addr {
                    Addr::Usize(old_b) | Addr::CutPoint(old_b) => {
                        let prev_b = self.stack.index_or_frame(self.b).prelude.b;
                        let prev_b = self.stack.index_or_frame(prev_b).prelude.b;

                        if prev_b > old_b {
                            self.fail = true;
                        }
                    }
                    _ => self.fail = true,
                };
            }
            &SystemClauseType::CopyTermWithoutAttrVars => {
                self.copy_term(AttrVarPolicy::StripAttributes);
            }
            &SystemClauseType::FetchGlobalVar => {
                let key = self[temp_v!(1)];

                let key = match self.store(self.deref(key)) {
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(ref atom, _) = &self.heap[h] {
                            atom.clone()
                        } else {
                            unreachable!()
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                };

                let addr = self[temp_v!(2)];

                match indices.global_variables.get_mut(&key) {
                    Some((ref mut ball, None)) => {
                        let h = self.heap.h();
                        let stub = ball.copy_and_align(h);

                        self.heap.extend(stub.into_iter());
                        self.unify(addr, Addr::HeapCell(h));
                    }
                    Some((_, Some(h))) => {
                        self.unify(addr, Addr::HeapCell(*h))
                    }
                    None => self.fail = true,
                };
            }
            &SystemClauseType::FetchGlobalVarWithOffset => {
                let key = self[temp_v!(1)];

                let key = match self.store(self.deref(key)) {
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(ref atom, _) = &self.heap[h] {
                            atom.clone()
                        } else {
                            unreachable!()
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                };

                let addr = self[temp_v!(2)];

                match indices.global_variables.get_mut(&key) {
                    Some((ref mut ball, ref mut offset @ None)) => {
                        let h = self.heap.h();
                        let stub = ball.copy_and_align(h);

                        self.heap.extend(stub.into_iter());
                        self.unify(addr, Addr::HeapCell(h));

                        *offset = Some(h);
                    }
                    Some((_, Some(h))) => {
                        let offset = self[temp_v!(3)];

                        self.unify(offset, Addr::Usize(*h));

                        if !self.fail {
                            self.unify(addr, Addr::HeapCell(*h));
                        }
                    }
                    None => {
                        self.fail = true
                    }
                };
            }
            &SystemClauseType::FileToChars => {
                // TODO: Replace this with stream.
                let a1 = self.store(self.deref(self[temp_v!(1)]));
                let a2 = self.store(self.deref(self[temp_v!(2)]));

                let file_name = match a1 {
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(name, _) = &self.heap[h] {
                            name.clone()
                        }
                        else {
                            unreachable!()
                        }
                    }
                    Addr::Char(c) => {
                        clause_name!(c.to_string(), indices.atom_tbl.clone())
                    }
                    _ => {
                        unreachable!()
                    }
                };

                let name = clause_name!("$file_to_chars");
                let mut file = match File::open(file_name.as_str()) {
                    Ok(f) => f,
                    Err(e) => {
                        let arity = 2;
                        let stub = MachineError::functor_stub(name.clone(), arity);
                        let h = self.heap.h();

                        let err = match e.kind() {
                            ErrorKind::NotFound => {
                                MachineError::existence_error(
                                    h,
                                    ExistenceError::ModuleSource(
                                        ModuleSource::File(file_name)
                                    ),
                                )
                            }
                            ErrorKind::PermissionDenied => {
                                let source_sink = self.store(self.deref(a1));

                                MachineError::permission_error(
                                    h,
                                    Permission::Access,
                                    "source_sink",
                                    source_sink
                                )
                            }
                            _ => unreachable!()  // Not nice.
                        };

                        return Err(self.error_form(err, stub));
                    }
                };


                let type_str = match self.store(self.deref(self[temp_v!(3)])) {
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(ref atom, _) = &self.heap[h] {
                            atom.as_str()
                        } else {
                            unreachable!()
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                };

                let complete_string = {
                    let mut buffer = String::new();
                    match type_str {
                        "text" => {  match file.read_to_string(&mut buffer) {
                                         Ok(_size) => {
                                             self.heap.put_complete_string(&buffer)
                                         }
                                         Err(_e) => {
                                            // the data isn't valid UTF-8, so we fail.
                                           self.fail = true;
                                           return Ok(());

                                         }
                                     }
                                  }
                        "binary" => { let mut buffer = Vec::new();
                                      let _ = match file.read_to_end(&mut buffer) {
                                          Ok(size) => size,
                                          Err(_e) => unreachable!()
                                      };

                                      let buffer = String::from_iter(
                                          buffer.into_iter().map(|b| b as char)
                                      );

                                      self.heap.put_complete_string(&buffer)
                                    }
                         _ => { unreachable!() }
                         }
                    };

                self.unify(complete_string, a2);
            }
            &SystemClauseType::PutCode => {
                let mut stream =
                    self.get_stream_or_alias(self[temp_v!(1)], indices, "put_code", 2)?;

                self.check_stream_properties(
                    &mut stream,
                    StreamType::Text,
                    None,
                    clause_name!("put_code"),
                    2,
                )?;

                match self.store(self.deref(self[temp_v!(2)])) {
                    addr if addr.is_ref() => {
                        let stub = MachineError::functor_stub(clause_name!("put_code"), 2);
                        let err = MachineError::instantiation_error();

                        return Err(self.error_form(err, stub));
                    }
                    addr => {
                        match Number::try_from((addr, &self.heap)) {
                            Ok(Number::Integer(n)) => {
                                if let Some(c) = n.to_u32().and_then(|c| char::try_from(c).ok()) {
                                    write!(&mut stream, "{}", c).unwrap();
                                    return return_from_clause!(self.last_call, self);
                                }
                            }
                            Ok(Number::Fixnum(n)) => {
                                if let Some(c) = u32::try_from(n).ok().and_then(|c| char::try_from(c).ok()) {
                                    write!(&mut stream, "{}", c).unwrap();
                                    return return_from_clause!(self.last_call, self);
                                }
                            }
                            _ => {
                                let stub = MachineError::functor_stub(clause_name!("put_code"), 2);
                                let err = MachineError::type_error(
                                    self.heap.h(),
                                    ValidType::Integer,
                                    self[temp_v!(2)],
                                );

                                return Err(self.error_form(err, stub));
                            }
                        }

                        let stub = MachineError::functor_stub(clause_name!("put_code"), 2);
                        let err = MachineError::representation_error(
                            RepFlag::CharacterCode,
                        );

                        return Err(self.error_form(err, stub));
                    }
                }
            }
            &SystemClauseType::PutChar => {
                let mut stream =
                    self.get_stream_or_alias(self[temp_v!(1)], indices, "put_char", 2)?;

                self.check_stream_properties(
                    &mut stream,
                    StreamType::Text,
                    None,
                    clause_name!("put_char"),
                    2,
                )?;

                match self.store(self.deref(self[temp_v!(2)])) {
                    addr if addr.is_ref() => {
                        let stub = MachineError::functor_stub(clause_name!("put_char"), 2);
                        let err = MachineError::instantiation_error();

                        return Err(self.error_form(err, stub));
                    }
                    addr => {
                        match self.store(self.deref(self[temp_v!(2)])) {
                            Addr::Con(h) if self.heap.atom_at(h) => {
                                match &self.heap[h] {
                                    HeapCellValue::Atom(ref atom, _) if atom.is_char() => {
                                        if let Some(c) = atom.as_str().chars().next() {
                                            write!(&mut stream, "{}", c).unwrap();
                                            return return_from_clause!(self.last_call, self);
                                        } else {
                                            unreachable!()
                                        }
                                    }
                                    _ => {
                                        unreachable!()
                                    }
                                }
                            }
                            Addr::Char(c) => {
                                write!(&mut stream, "{}", c).unwrap();
                                return return_from_clause!(self.last_call, self);
                            }
                            _ => {
                            }
                        }

                        let stub = MachineError::functor_stub(clause_name!("put_char"), 2);
                        let err = MachineError::type_error(
                            self.heap.h(),
                            ValidType::Character,
                            addr,
                        );

                        return Err(self.error_form(err, stub));
                    }
                }
            }
            &SystemClauseType::PutByte => {
                let mut stream =
                    self.get_stream_or_alias(self[temp_v!(1)], indices, "put_byte", 2)?;

                self.check_stream_properties(
                    &mut stream,
                    StreamType::Binary,
                    None,
                    clause_name!("put_byte"),
                    2,
                )?;

                match self.store(self.deref(self[temp_v!(2)])) {
                    addr if addr.is_ref() => {
                        let stub = MachineError::functor_stub(clause_name!("put_byte"), 2);
                        let err = MachineError::instantiation_error();

                        return Err(self.error_form(err, stub));
                    }
                    addr => {
                        match Number::try_from((addr, &self.heap)) {
                            Ok(Number::Integer(n)) => {
                                if let Some(nb) = n.to_u8() {
                                    match stream.write(&mut [nb]) {
                                        Ok(1) => {
                                            return return_from_clause!(self.last_call, self);
                                        }
                                        _ => {
                                            let stub = MachineError::functor_stub(
                                                clause_name!("put_byte"),
                                                2,
                                            );

                                            let addr = self.heap.to_unifiable(
                                                HeapCellValue::Stream(stream.clone()),
                                            );

                                            return Err(self.error_form(
                                                MachineError::existence_error(
                                                    self.heap.h(),
                                                    ExistenceError::Stream(addr),
                                                ),
                                                stub,
                                            ));
                                        }
                                    }
                                }
                            }
                            Ok(Number::Fixnum(n)) => {
                                if let Ok(nb) = u8::try_from(n) {
                                    match stream.write(&mut [nb]) {
                                        Ok(1) => {
                                            return return_from_clause!(self.last_call, self);
                                        }
                                        _ => {
                                            let stub = MachineError::functor_stub(
                                                clause_name!("put_byte"),
                                                2,
                                            );

                                            let addr = self.heap.to_unifiable(
                                                HeapCellValue::Stream(stream.clone()),
                                            );

                                            return Err(self.error_form(
                                                MachineError::existence_error(
                                                    self.heap.h(),
                                                    ExistenceError::Stream(addr),
                                                ),
                                                stub,
                                            ));
                                        }
                                    }
                                }
                            }
                            _ => {
                            }
                        }

                        let stub = MachineError::functor_stub(clause_name!("put_byte"), 2);
                        let err = MachineError::type_error(
                            self.heap.h(),
                            ValidType::Byte,
                            self[temp_v!(2)],
                        );

                        return Err(self.error_form(err, stub));
                    }
                }
            }
            &SystemClauseType::GetByte => {
                let mut stream =
                    self.get_stream_or_alias(self[temp_v!(1)], indices, "get_byte", 2)?;

                self.check_stream_properties(
                    &mut stream,
                    StreamType::Binary,
                    Some(self[temp_v!(2)]),
                    clause_name!("get_byte"),
                    2,
                )?;

                if stream.past_end_of_stream() {
                    if EOFAction::Reset != stream.options.eof_action {
                        return return_from_clause!(self.last_call, self);
                    } else if self.fail {
                        return Ok(());
                    }
                }

                if stream.at_end_of_stream() {
                    stream.set_past_end_of_stream();
                    self.unify(self[temp_v!(2)], Addr::Fixnum(-1));
                    return return_from_clause!(self.last_call, self);
                }

                let addr =
                    match self.store(self.deref(self[temp_v!(2)])) {
                        addr if addr.is_ref() => {
                            addr
                        }
                        addr => {
                            match Number::try_from((addr, &self.heap)) {
                                Ok(Number::Integer(n)) => {
                                    if let Some(nb) = n.to_u8() {
                                        Addr::Usize(nb as usize)
                                    } else {
                                        return Err(self.type_error(
                                            ValidType::InByte,
                                            addr,
                                            clause_name!("get_byte"),
                                            2,
                                        ));
                                    }
                                }
                                Ok(Number::Fixnum(n)) => {
                                    if let Ok(nb) = u8::try_from(n) {
                                        Addr::Usize(nb as usize)
                                    } else {
                                        return Err(self.type_error(
                                            ValidType::InByte,
                                            addr,
                                            clause_name!("get_byte"),
                                            2,
                                        ));
                                    }
                                }
                                _ => {
                                    return Err(self.type_error(
                                        ValidType::InByte,
                                        addr,
                                        clause_name!("get_byte"),
                                        2,
                                    ));
                                }
                            }
                        }
                    };

                loop {
                    let mut b = [0u8; 1];

                    match stream.read(&mut b) {
                        Ok(1) => {
                            if let Some(var) = addr.as_var() {
                                self.bind(var, Addr::Usize(b[0] as usize));
                                break;
                            } else if addr == Addr::Usize(b[0] as usize) {
                                break;
                            } else {
                                self.fail = true;
                                return Ok(());
                            }
                        }
                        _ => {
                            self.eof_action(
                                self[temp_v!(2)],
                                &mut stream,
                                clause_name!("get_byte"),
                                2,
                            )?;

                            if EOFAction::Reset != stream.options.eof_action {
                                return return_from_clause!(self.last_call, self);
                            } else if self.fail {
                                return Ok(());
                            }
                        }
                    }
                }
            }
            &SystemClauseType::GetChar => {
                let mut stream =
                    self.get_stream_or_alias(self[temp_v!(1)], indices, "get_char", 2)?;

                self.check_stream_properties(
                    &mut stream,
                    StreamType::Text,
                    Some(self[temp_v!(2)]),
                    clause_name!("get_char"),
                    2,
                )?;

                if stream.past_end_of_stream() {
                    if EOFAction::Reset != stream.options.eof_action {
                        return return_from_clause!(self.last_call, self);
                    } else if self.fail {
                        return Ok(());
                    }
                }

                if stream.at_end_of_stream() {
                    let end_of_file = clause_name!("end_of_file");
                    let end_of_file = self.heap.to_unifiable(
                        HeapCellValue::Atom(end_of_file, None),
                    );

                    stream.set_past_end_of_stream();

                    self.unify(self[temp_v!(2)], end_of_file);
                    return return_from_clause!(self.last_call, self);
                }

                let mut iter = self.open_parsing_stream(
                    stream.clone(),
                    "get_char",
                    2,
                )?;

                let addr =
                    match self.store(self.deref(self[temp_v!(2)])) {
                        addr if addr.is_ref() => {
                            addr
                        }
                        Addr::Con(h) if self.heap.atom_at(h) => {
                            match &self.heap[h] {
                                HeapCellValue::Atom(ref atom, _) if atom.is_char() => {
                                    if let Some(c) = atom.as_str().chars().next() {
                                        Addr::Char(c)
                                    } else {
                                        unreachable!()
                                    }
                                }
                                culprit => {
                                    return Err(self.type_error(
                                        ValidType::InCharacter,
                                        culprit.as_addr(h),
                                        clause_name!("get_char"),
                                        2,
                                    ));
                                }
                            }
                        }
                        Addr::Char(d) => {
                            Addr::Char(d)
                        }
                        culprit => {
                            return Err(self.type_error(
                                ValidType::InCharacter,
                                culprit,
                                clause_name!("get_char"),
                                2,
                            ));
                        }
                    };

                loop {
                    let result = iter.next();

                    match result {
                        Some(Ok(d)) => {
                            if let Some(var) = addr.as_var() {
                                self.bind(var, Addr::Char(d));
                                break;
                            } else if addr == Addr::Char(d) {
                                break;
                            } else {
                                self.fail = true;
                                return Ok(());
                            }
                        }
                        _ => {
                            self.eof_action(
                                self[temp_v!(2)],
                                &mut stream,
                                clause_name!("get_char"),
                                2,
                            )?;

                            if EOFAction::Reset != stream.options.eof_action {
                                return return_from_clause!(self.last_call, self);
                            } else if self.fail {
                                return Ok(());
                            }
                        }/*
                        _ => {
                            let stub = MachineError::functor_stub(clause_name!("get_char"), 2);
                            let err = MachineError::representation_error(RepFlag::Character);
                            let err = self.error_form(err, stub);

                            return Err(err);
                        }*/
                    }
                }
            }
            &SystemClauseType::GetCode => {
                let mut stream =
                    self.get_stream_or_alias(self[temp_v!(1)], indices, "get_code", 2)?;

                self.check_stream_properties(
                    &mut stream,
                    StreamType::Text,
                    Some(self[temp_v!(2)]),
                    clause_name!("get_code"),
                    2,
                )?;

                if stream.past_end_of_stream() {
                    if EOFAction::Reset != stream.options.eof_action {
                        return return_from_clause!(self.last_call, self);
                    } else if self.fail {
                        return Ok(());
                    }
                }

                if stream.at_end_of_stream() {
                    let end_of_file = clause_name!("end_of_file");
                    let end_of_file = self.heap.to_unifiable(
                        HeapCellValue::Atom(end_of_file, None),
                    );

                    stream.set_past_end_of_stream();

                    self.unify(self[temp_v!(2)], end_of_file);
                    return return_from_clause!(self.last_call, self);
                }

                let addr =
                    match self.store(self.deref(self[temp_v!(2)])) {
                        addr if addr.is_ref() => {
                            addr
                        }
                        addr => {
                            match Number::try_from((addr, &self.heap)) {
                                Ok(Number::Integer(n)) => {
                                    let n = n.to_u32().and_then(|n| {
                                        std::char::from_u32(n).and_then(|_| Some(n))
                                    });

                                    if let Some(n) = n {
                                        Addr::Fixnum(n as isize)
                                    } else {
                                        return Err(self.representation_error(
                                            RepFlag::InCharacterCode,
                                            clause_name!("get_code"),
                                            2,
                                        ));
                                    }
                                }
                                Ok(Number::Fixnum(n)) => {
                                    let n = u32::try_from(n).ok().and_then(|n| {
                                        std::char::from_u32(n).and_then(|_| Some(n))
                                    });

                                    if let Some(n) = n {
                                        Addr::Fixnum(n as isize)
                                    } else {
                                        return Err(self.representation_error(
                                            RepFlag::InCharacterCode,
                                            clause_name!("get_code"),
                                            2,
                                        ));
                                    }
                                }
                                _ => {
                                    return Err(self.type_error(
                                        ValidType::Integer,
                                        self[temp_v!(2)],
                                        clause_name!("get_code"),
                                        2,
                                    ));
                                }
                            }
                        }
                    };

                let mut iter = self.open_parsing_stream(
                    stream.clone(),
                    "get_code",
                    2,
                )?;

                loop {
                    let result = iter.next();

                    match result {
                        Some(Ok(c)) => {
                            if let Some(var) = addr.as_var() {
                                self.bind(var, Addr::Fixnum(c as isize));
                                break;
                            } else if addr == Addr::Fixnum(c as isize) {
                                break;
                            } else {
                                self.fail = true;
                                return Ok(());
                            }
                        }
                        _ => {
                            self.eof_action(
                                self[temp_v!(2)],
                                &mut stream,
                                clause_name!("get_code"),
                                2,
                            )?;

                            if EOFAction::Reset != stream.options.eof_action {
                                return return_from_clause!(self.last_call, self);
                            } else if self.fail {
                                return Ok(());
                            }
                        }/*
                        _ => {
                            let stub = MachineError::functor_stub(clause_name!("get_char"), 2);
                            let err = MachineError::representation_error(RepFlag::Character);
                            let err = self.error_form(err, stub);

                            return Err(err);
                        }*/
                    }
                }
            }
            &SystemClauseType::FirstStream => {
                let mut first_stream = None;
                let mut null_streams = BTreeSet::new();

                for stream in indices.streams.iter().cloned() {
                    if !stream.is_null_stream() {
                        first_stream = Some(stream);
                        break;
                    } else {
                        null_streams.insert(stream);
                    }
                }

                indices.streams = indices.streams.sub(&null_streams);

                if let Some(first_stream) = first_stream {
                    let stream = self.heap.to_unifiable(HeapCellValue::Stream(first_stream));

                    let var = self.store(self.deref(self[temp_v!(1)])).as_var().unwrap();
                    self.bind(var, stream);
                } else {
                    self.fail = true;
                    return Ok(());
                }
            }
            &SystemClauseType::NextStream => {
                let prev_stream =
                    match self.store(self.deref(self[temp_v!(1)])) {
                        Addr::Stream(h) => {
                            if let HeapCellValue::Stream(ref stream) = &self.heap[h] {
                                stream.clone()
                            } else {
                                unreachable!()
                            }
                        }
                        _ => {
                            unreachable!()
                        }
                    };

                let mut next_stream  = None;
                let mut null_streams = BTreeSet::new();

                for stream in indices.streams.range(prev_stream.clone() ..).skip(1).cloned() {
                    if !stream.is_null_stream() {
                        next_stream = Some(stream);
                        break;
                    } else {
                        null_streams.insert(stream);
                    }
                }

                indices.streams = indices.streams.sub(&null_streams);

                if let Some(next_stream) = next_stream {
                    let var = self.store(self.deref(self[temp_v!(2)])).as_var().unwrap();
                    let next_stream = self.heap.to_unifiable(HeapCellValue::Stream(next_stream));

                    self.bind(var, next_stream);
                } else {
                    self.fail = true;
                    return Ok(());
                }
            }
            &SystemClauseType::FlushOutput => {
                let mut stream =
                    self.get_stream_or_alias(self[temp_v!(1)], indices, "flush_output", 1)?;

                if !stream.is_output_stream() {
                    let stub = MachineError::functor_stub(clause_name!("flush_output"), 1);

                    let addr = vec![
                        HeapCellValue::Stream(stream)
                    ];

                    let err = MachineError::permission_error(
                        self.heap.h(),
                        Permission::OutputStream,
                        "stream",
                        addr,
                    );

                    return Err(self.error_form(err, stub));
                }

                stream.flush().unwrap();
            }
            &SystemClauseType::GetSingleChar => {
                let ctrl_c = KeyEvent {
                    code: KeyCode::Char('c'),
                    modifiers: KeyModifiers::CONTROL
                };
                let key = get_key();
                if key == ctrl_c {
                    let stub = MachineError::functor_stub(
                        clause_name!("get_single_char"),
                        1
                    );
                    let err = MachineError::interrupt_error();
                    let err = self.error_form(err, stub);

                    return Err(err);
                }
                let c = match key.code {
                    KeyCode::Enter => '\n',
                    KeyCode::Tab => '\t',
                    KeyCode::Char(c) => c,
                    _ => unreachable!()
                };

                let a1 = self[temp_v!(1)];

                self.unify(Addr::Char(c), a1);
            }
            &SystemClauseType::GetModuleClause => {
                let module = self[temp_v!(3)];
                let head = self[temp_v!(1)];

                let module = match self.store(self.deref(module)) {
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(module, _) = &self.heap[h] {
                            module.clone()
                        } else {
                            unreachable!()
                        }
                    }
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                };

                let subsection = match self.store(self.deref(head)) {
                    Addr::Str(s) => match &self.heap[s] {
                        &HeapCellValue::NamedStr(arity, ref name, ..) => {
                            indices.get_clause_subsection(module, name.clone(), arity)
                        }
                        _ => {
                            unreachable!()
                        }
                    },
                    Addr::Con(h) => {
	                if let HeapCellValue::Atom(name, _) = &self.heap[h] {
                            indices.get_clause_subsection(module, name.clone(), 0)
                        } else {
                            unreachable!()
                        }
                    }

                    _ => {
                        unreachable!()
                    }
                };

                match subsection {
                    Some(dynamic_predicate_info) => {
                        self.execute_at_index(
                            2,
                            dir_entry!(dynamic_predicate_info.clauses_subsection_p),
                        );

                        return Ok(());
                    }
                    None => {
                        self.fail = true;
                    }
                }
            }
            &SystemClauseType::ModuleHeadIsDynamic => {
                let module = self[temp_v!(2)];
                let head = self[temp_v!(1)];

                let module = match self.store(self.deref(module)) {
                    Addr::Con(h) if self.heap.atom_at(h) =>
                        if let HeapCellValue::Atom(module, _) = &self.heap[h] {
                            module.clone()
                        } else {
                            unreachable!()
                        }
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                };

                self.fail = !match self.store(self.deref(head)) {
                    Addr::Str(s) => match &self.heap[s] {
                        &HeapCellValue::NamedStr(arity, ref name, ..) => {
                            indices.get_clause_subsection(module, name.clone(), arity)
                                   .is_some()
                        }
                        _ => unreachable!(),
                    },
                    Addr::Con(h) => {
	                if let HeapCellValue::Atom(name, _) = &self.heap[h] {
                            indices.get_clause_subsection(module, name.clone(), 0)
                                   .is_some()
                        } else {
                            unreachable!()
                        }
                    }
                    _ => unreachable!(),
                };
            }
            &SystemClauseType::HeadIsDynamic => {
                let head = self[temp_v!(1)];

                self.fail = !match self.store(self.deref(head)) {
                    Addr::Str(s) => match &self.heap[s] {
                        &HeapCellValue::NamedStr(arity, ref name, ..) => indices
                            .get_clause_subsection(name.owning_module(), name.clone(), arity)
                            .is_some(),
                        _ => unreachable!(),
                    },
                    Addr::Con(h) if self.heap.atom_at(h) => {
	                if let HeapCellValue::Atom(name, _) = &self.heap[h] {
                            indices.get_clause_subsection(name.owning_module(), name.clone(), 0)
                                   .is_some()
                        } else {
                            unreachable!()
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                };
            }
            &SystemClauseType::Close => {
                let mut stream =
                    self.get_stream_or_alias(self[temp_v!(1)], indices, "close", 2)?;

                if !stream.is_input_stream() {
                    stream.flush().unwrap(); // 8.11.6.1b)
                }

                indices.streams.remove(&stream);

                if stream == *current_input_stream {
                    *current_input_stream = indices.stream_aliases.get(
                        &clause_name!("user_input")
                    ).cloned().unwrap();

                    indices.streams.insert(current_input_stream.clone());
                } else if stream == *current_output_stream {
                    *current_output_stream = indices.stream_aliases.get(
                        &clause_name!("user_output")
                    ).cloned().unwrap();

                    indices.streams.insert(current_output_stream.clone());
                }

                if !stream.is_stdin() && !stream.is_stdout() {
                    stream.close();

                    if let Some(alias) = stream.options.alias {
                        indices.stream_aliases.remove(&alias);
                    }
                }
            }
            &SystemClauseType::CopyToLiftedHeap => {
                match self.store(self.deref(self[temp_v!(1)])) {
                    Addr::Usize(lh_offset) => {
                        let copy_target = self[temp_v!(2)];

                        let old_threshold = self.copy_findall_solution(lh_offset, copy_target);
                        let new_threshold = self.lifted_heap.h() - lh_offset;

                        self.lifted_heap[old_threshold] =
                            HeapCellValue::Addr(Addr::HeapCell(new_threshold));

                        for addr in self.lifted_heap.iter_mut_from(old_threshold + 1) {
                            match addr {
                                HeapCellValue::Addr(ref mut addr) => {
                                    *addr -= self.heap.h() + lh_offset;
                                }
                                _ => {}
                            }
                        }
                    }
                    _ => {
                        self.fail = true;
                    }
                }
            }
            &SystemClauseType::DeleteAttribute => {
                let ls0 = self.store(self.deref(self[temp_v!(1)]));

                if let Addr::Lis(l1) = ls0 {
                    if let Addr::Lis(l2) = self.store(self.deref(Addr::HeapCell(l1 + 1))) {
                        let old_addr = self.heap[l1 + 1].as_addr(l1 + 1);
                        let tail = self.store(self.deref(Addr::HeapCell(l2 + 1)));

                        let tail = if tail.is_ref() {
                            Addr::HeapCell(l1 + 1)
                        } else {
                            tail
                        };

                        let trail_ref = match old_addr {
                            Addr::HeapCell(h) => TrailRef::AttrVarHeapLink(h),
                            Addr::Lis(l) => TrailRef::AttrVarListLink(l1 + 1, l),
                            _ => unreachable!()
                        };

                        self.heap[l1 + 1] = HeapCellValue::Addr(tail);
                        self.trail(trail_ref);
                    }
                }
            }
            &SystemClauseType::DeleteHeadAttribute => {
                let addr = self.store(self.deref(self[temp_v!(1)]));

                match addr {
                    Addr::AttrVar(h) => {
                        let addr = self.heap[h + 1].as_addr(h + 1);
                        let addr = self.store(self.deref(addr));

                        match addr {
                            Addr::Lis(l) => {
                                let tail = self.store(self.deref(Addr::HeapCell(l + 1)));
                                let tail = if tail.is_ref() {
                                    self.heap[h] = HeapCellValue::Addr(Addr::HeapCell(h));
                                    self.trail(TrailRef::Ref(Ref::AttrVar(h)));

                                    Addr::HeapCell(h + 1)
                                } else {
                                    tail
                                };

                                self.heap[h + 1] = HeapCellValue::Addr(tail);
                                self.trail(TrailRef::AttrVarListLink(h + 1, l));
                            }
                            _ => {
                                unreachable!();
                            }
                        }
                    }
                    _ => {
                        unreachable!();
                    }
                }
            }
            &SystemClauseType::DynamicModuleResolution(narity) => {
                let module_name = self.store(self.deref(self[temp_v!(1 + narity)]));

                let module_name = match module_name {
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(ref module_name, _) = self.heap[h] {
                            module_name.clone()
                        } else {
                            unreachable!()
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                };

                match self.store(self.deref(self[temp_v!(2 + narity)])) {
                    Addr::Str(a) => {
                        if let HeapCellValue::NamedStr(arity, name, _) = self.heap.clone(a) {
                            for i in (arity + 1 .. arity + narity + 1).rev() {
                                self.registers[i] = self.registers[i - arity];
                            }

                            for i in 1 .. arity + 1 {
                                self.registers[i] = self.heap[a + i].as_addr(a + i);
                            }

                            return self.module_lookup(
                                indices,
                                (name, arity + narity),
                                module_name,
                                true,
                            );
                        } else {
                            unreachable!()
                        }
                    }
                    Addr::Con(h) if self.heap.atom_at(h) => {
	                if let HeapCellValue::Atom(name, _) = self.heap.clone(h) {
                            return self.module_lookup(
                                indices,
                                (name.clone(), narity),
                                module_name,
                                true,
                            );
                        } else {
                            unreachable!()
                        }
                    }
                    addr => {
                        let stub = MachineError::functor_stub(clause_name!("(:)"), 2);

                        let type_error = MachineError::type_error(
                            self.heap.h(),
                            ValidType::Callable,
                            addr,
                        );

                        let type_error = self.error_form(type_error, stub);
                        return Err(type_error);
                    }
                }
            }
            &SystemClauseType::EnqueueAttributeGoal => {
                let addr = self[temp_v!(1)];
                self.attr_var_init.attribute_goals.push(addr);
            }
            &SystemClauseType::EnqueueAttributedVar => {
                let addr = self[temp_v!(1)];

                match self.store(self.deref(addr)) {
                    Addr::AttrVar(h) => {
                        self.attr_var_init.attr_var_queue.push(h);
                    }
                    _ => {
                    }
                }
            }
            &SystemClauseType::ExpandGoal => {
                self.p = CodePtr::Local(LocalCodePtr::UserGoalExpansion(0));
                return Ok(());
            }
            &SystemClauseType::ExpandTerm => {
                self.p = CodePtr::Local(LocalCodePtr::UserTermExpansion(0));
                return Ok(());
            }
            &SystemClauseType::GetNextDBRef => {
                let a1 = self[temp_v!(1)];

                match self.store(self.deref(a1)) {
                    addr @ Addr::HeapCell(_)
                  | addr @ Addr::StackCell(..)
                  | addr @ Addr::AttrVar(_) => {
                        let mut iter = indices.code_dir.iter();

                        while let Some(((name, arity), _)) = iter.next() {
                            if is_builtin_predicate(&name) {
                                continue;
                            }

                            let spec = get_clause_spec(
                                name.clone(),
                                *arity,
                                composite_op!(&indices.op_dir),
                            );

                            let db_ref = DBRef::NamedPred(name.clone(), *arity, spec);
                            let r = addr.as_var().unwrap();

                            let addr = self.heap.to_unifiable(
                                HeapCellValue::DBRef(db_ref)
                            );

                            self.bind(r, addr);

                            return return_from_clause!(self.last_call, self);
                        }

                        self.fail = true;
                    }
                    Addr::Con(h) => {
                        match self.heap.clone(h) {
                            HeapCellValue::DBRef(DBRef::Op(..)) => {
                                self.fail = true;
                            }
                            HeapCellValue::DBRef(ref db_ref) => {
                                self.get_next_db_ref(indices, db_ref);
                            }
                            _ => {
                                self.fail = true;
                            }
                        }
                    }
                    _ => {
                        self.fail = true;
                    }
                }
            }
            &SystemClauseType::GetNextOpDBRef => {
                let a1 = self[temp_v!(1)];

                match self.store(self.deref(a1)) {
                    addr @ Addr::HeapCell(_)
                  | addr @ Addr::StackCell(..)
                  | addr @ Addr::AttrVar(_) => {
                        let mut unossified_op_dir = OssifiedOpDir::new();

                        unossified_op_dir.extend(indices.op_dir.iter().filter_map(
                            |(key, op_dir_val)| {
                                let (name, fixity) = key.clone();

                                let prec = op_dir_val.shared_op_desc().prec();

                                if prec == 0 {
                                    return None;
                                }

                                let assoc = op_dir_val.shared_op_desc().assoc();

                                Some((OrderedOpDirKey(name, fixity), (prec, assoc)))
                            },
                        ));

                        let ossified_op_dir = Rc::new(unossified_op_dir);

                        match ossified_op_dir.iter().next() {
                            Some((OrderedOpDirKey(name, _), (priority, spec))) => {
                                let db_ref = DBRef::Op(
                                    *priority,
                                    *spec,
                                    name.clone(),
                                    ossified_op_dir.clone(),
                                    SharedOpDesc::new(*priority, *spec),
                                );

                                let r = addr.as_var().unwrap();
                                let addr = self.heap.to_unifiable(
                                    HeapCellValue::DBRef(db_ref)
                                );

                                self.bind(r, addr);
                            }
                            None => {
                                self.fail = true;
                                return Ok(());
                            }
                        }
                    }
                    Addr::Con(h) => {
                        match self.heap.clone(h) {
                            HeapCellValue::DBRef(DBRef::NamedPred(..)) => {
                                self.fail = true;
                            }
                            HeapCellValue::DBRef(ref db_ref) => {
                                self.get_next_db_ref(indices, db_ref);
                            }
                            _ => {
                                self.fail = true;
                            }
                        }
                    }
                    _ => {
                        self.fail = true;
                    }
                }
            }
            &SystemClauseType::LookupDBRef => {
                let a1 = self[temp_v!(1)];

                match self.store(self.deref(a1)) {
                    Addr::Con(h) => {
                        match self.heap.clone(h) {
                            HeapCellValue::DBRef(DBRef::NamedPred(name, arity, spec)) => {
                                let a2 = self[temp_v!(2)];
                                let a3 = self[temp_v!(3)];

                                let atom = self.heap.to_unifiable(
                                    HeapCellValue::Atom(name, spec)
                                );

                                self.unify(a2, atom);

                                if !self.fail {
                                    self.unify(a3, Addr::Usize(arity));
                                }
                            }
                            _ => {
                                self.fail = true;
                            }
                        }
                    }
                    _ => {
                        self.fail = true;
                    }
                }
            }
            &SystemClauseType::LookupOpDBRef => {
                let a1 = self[temp_v!(1)];

                match self.store(self.deref(a1)) {
                    Addr::Con(h) => {
                        match self.heap.clone(h) {
                            HeapCellValue::DBRef(DBRef::Op(
                                priority,
                                spec,
                                name,
                                _,
                                shared_op_desc,
                            )) => {
                                let prec = self[temp_v!(2)];
                                let specifier = self[temp_v!(3)];
                                let op = self[temp_v!(4)];

                                let spec = match spec {
                                    FX => "fx",
                                    FY => "fy",
                                    XF => "xf",
                                    YF => "yf",
                                    XFX => "xfx",
                                    XFY => "xfy",
                                    YFX => "yfx",
                                    _ => {
                                        self.fail = true;
                                        return Ok(());
                                    }
                                };

                                let a3 = self.heap.to_unifiable(
                                    HeapCellValue::Atom(clause_name!(spec), None)
                                );

                                let a4 = self.heap.to_unifiable(
                                    HeapCellValue::Atom(name, Some(shared_op_desc))
                                );

                                self.unify(Addr::Usize(priority), prec);

                                if !self.fail {
                                    self.unify(a3, specifier);
                                }

                                if !self.fail {
                                    self.unify(a4, op);
                                }
                            }
                            _ => {
                                self.fail = true;
                            }
                        }
                    }
                    _ => {
                        self.fail = true;
                    }
                }
            }
            &SystemClauseType::Maybe => {
                let result = {
                    let mut rand = RANDOM_STATE.borrow_mut();
                    rand.bits(1) == 0
                };

                self.fail = result;
            }
            &SystemClauseType::CpuNow => {
                let a1 = self[temp_v!(1)];
                let a2 = ProcessTime::now().as_duration().as_secs_f64();
                let addr = self.heap.put_constant(Constant::Float(OrderedFloat(a2)));

                self.unify(a1, addr);
            }
            &SystemClauseType::OpDeclaration => {
                let priority = self[temp_v!(1)];
                let specifier = self[temp_v!(2)];
                let op = self[temp_v!(3)];

                let priority = self.store(self.deref(priority));

                let priority =
                    match Number::try_from((priority, &self.heap)) {
                        Ok(Number::Integer(n)) => {
                            n.to_usize().unwrap()
                        }
                        Ok(Number::Fixnum(n)) => {
                            usize::try_from(n).unwrap()
                        }
                        _ => {
                            unreachable!();
                        }
                    };

                let specifier = match self.store(self.deref(specifier)) {
                    Addr::Con(h) if self.heap.atom_at(h) =>
                        if let HeapCellValue::Atom(ref specifier, _) = &self.heap[h] {
                            specifier.clone()
                        } else {
                            unreachable!()
                        },
                    _ =>
                        unreachable!(),
                };

                let op = match self.store(self.deref(op)) {
                    Addr::Char(c) =>
                        clause_name!(c.to_string(), indices.atom_tbl),
                    Addr::Con(h) if self.heap.atom_at(h) =>
                        if let HeapCellValue::Atom(ref name, _) = &self.heap[h] {
                            name.clone()
                        } else {
                            unreachable!()
                        },
                    _ =>
                        unreachable!(),
                };

                let module = op.owning_module();

                let result = to_op_decl(priority, specifier.as_str(), op)
                    .map_err(SessionError::from)
                    .and_then(|op_decl| {
                        if op_decl.0 == 0 {
                            Ok(op_decl.remove(&mut indices.op_dir))
                        } else {
                            let spec = get_desc(op_decl.name(), composite_op!(&indices.op_dir));
                            op_decl.submit(module, spec, &mut indices.op_dir)
                        }
                    });

                match result {
                    Ok(()) => {
                    }
                    Err(e) => {
                        // 8.14.3.3 l)
                        let e = MachineError::session_error(self.heap.h(), e);
                        let stub = MachineError::functor_stub(clause_name!("op"), 3);
                        let permission_error = self.error_form(e, stub);

                        return Err(permission_error);
                    }
                };
            }
            &SystemClauseType::Open => {
                let alias = self[temp_v!(4)];
                let eof_action = self[temp_v!(5)];
                let reposition = self[temp_v!(6)];
                let stream_type = self[temp_v!(7)];

                let options =
                    self.to_stream_options(alias, eof_action, reposition, stream_type);

                let file_spec =
                    match self.store(self.deref(self[temp_v!(1)])) {
                        Addr::Con(h) if self.heap.atom_at(h) => {
                            match &self.heap[h] {
                                &HeapCellValue::Atom(ref atom, _) => {
                                    atom.clone()
                                }
                                _ => {
                                    unreachable!()
                                }
                            }
                        }
                        Addr::PStrLocation(h, n) => {
                            match &self.heap[h] {
                                &HeapCellValue::PartialString(_, true) => {
                                    let mut heap_pstr_iter =
                                        self.heap_pstr_iter(Addr::PStrLocation(h, n));

                                    clause_name!(
                                        heap_pstr_iter.to_string(),
                                        indices.atom_tbl.clone()
                                    )
                                }
                                _ => {
                                    clause_name!("")
                                }
                            }
                        }
                        _ => {
                            clause_name!("")
                        }
                    };

                if file_spec.as_str().is_empty() {
                    let stub = MachineError::functor_stub(clause_name!("open"), 4);
                    let err = MachineError::domain_error(
                        DomainErrorType::SourceSink,
                        self[temp_v!(1)],
                    );

                    return Err(self.error_form(err, stub));
                }

                // 8.11.5.3l)
                if let Some(ref alias) = &options.alias {
                    if indices.stream_aliases.contains_key(alias) {
                        return Err(self.occupied_alias_permission_error(
                            alias.clone(),
                            "open",
                            4,
                        ));
                    }
                }

                let mode =
                    atom_from!(self, indices, self.store(self.deref(self[temp_v!(2)])));

                let mut open_options = OpenOptions::new();

                let (is_input_file, in_append_mode) =
                    match mode.as_str() {
                        "read" => {
                            open_options.read(true).write(false).create(false);
                            (true, false)
                        }
                        "write" => {
                            open_options.read(false).write(true).truncate(true).create(true);
                            (false, false)
                        }
                        "append" => {
                            open_options.read(false).write(true).create(true).append(true);
                            (false, true)
                        }
                        _ => {
                            let stub = MachineError::functor_stub(clause_name!("open"), 4);
                            let err  = MachineError::domain_error(
                                DomainErrorType::IOMode,
                                self[temp_v!(2)],
                            );

                            // 8.11.5.3h)
                            return Err(self.error_form(err, stub));
                        }
                    };

                let file =
                    match open_options.open(file_spec.as_str()).map_err(|e| e.kind()) {
                        Ok(file) => {
                            file
                        }
                        Err(ErrorKind::NotFound) => {
                            // 8.11.5.3j)
                            let stub = MachineError::functor_stub(
                                clause_name!("open"),
                                4,
                            );

                            let err = MachineError::existence_error(
                                self.heap.h(),
                                ExistenceError::SourceSink(self[temp_v!(1)]),
                            );

                            return Err(self.error_form(err, stub));
                        }
                        Err(ErrorKind::PermissionDenied) => {
                            // 8.11.5.3k)
                            return Err(self.open_permission_error(self[temp_v!(1)], "open", 4));
                        }
                        Err(_) => {
                            // for now, just fail. expand to meaningful error messages later.
                            self.fail = true;
                            return Ok(());
                        }
                    };

                let mut stream = if is_input_file {
                    Stream::from_file_as_input(file_spec, file)
                } else {
                    Stream::from_file_as_output(file_spec, file, in_append_mode)
                };

                stream.options = options;

                indices.streams.insert(stream.clone());

                if let Some(ref alias) = &stream.options.alias {
                    indices.stream_aliases.insert(alias.clone(), stream.clone());
                }

                let stream = self.heap.to_unifiable(HeapCellValue::Stream(stream));
                let stream_var = self.store(self.deref(self[temp_v!(3)]));

                self.bind(stream_var.as_var().unwrap(), stream);
            }
            &SystemClauseType::TruncateIfNoLiftedHeapGrowthDiff => {
                self.truncate_if_no_lifted_heap_diff(|h| Addr::HeapCell(h))
            }
            &SystemClauseType::TruncateIfNoLiftedHeapGrowth => {
                self.truncate_if_no_lifted_heap_diff(|_| Addr::EmptyList)
            }
            &SystemClauseType::ClearAttributeGoals => {
                self.attr_var_init.attribute_goals.clear();
            }
            &SystemClauseType::CloneAttributeGoals => {
                let attr_goals = self.attr_var_init.attribute_goals.clone();
                self.fetch_attribute_goals(attr_goals);
            }
            &SystemClauseType::GetAttributedVariableList => {
                let attr_var = self.store(self.deref(self[temp_v!(1)]));
                let attr_var_list =
                    match attr_var {
                        Addr::AttrVar(h) => {
                            h + 1
                        }
                        attr_var @ Addr::HeapCell(_) |
                        attr_var @ Addr::StackCell(..) => {
                            // create an AttrVar in the heap.
                            let h = self.heap.h();

                            self.heap.push(HeapCellValue::Addr(Addr::AttrVar(h)));
                            self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h + 1)));

                            self.bind(Ref::AttrVar(h), attr_var);
                            h + 1
                        }
                        _ => {
                            self.fail = true;
                            return Ok(());
                        }
                    };

                let list_addr = self[temp_v!(2)];
                self.bind(Ref::HeapCell(attr_var_list), list_addr);
            }
            &SystemClauseType::GetAttrVarQueueDelimiter => {
                let addr = self[temp_v!(1)];
                let value = Addr::Usize(self.attr_var_init.attr_var_queue.len());

                self.unify(addr, value);
            }
            &SystemClauseType::GetAttrVarQueueBeyond => {
                let addr = self[temp_v!(1)];
                let addr = self.store(self.deref(addr));

                let b =
                    match addr {
                        Addr::Usize(b) => {
                            Some(b)
                        }
                        _ => {
                            match Number::try_from((addr, &self.heap)) {
                                Ok(Number::Integer(n)) => {
                                    n.to_usize()
                                }
                                Ok(Number::Fixnum(n)) => {
                                    usize::try_from(n).ok()
                                }
                                _ => {
                                    self.fail = true;
                                    return Ok(());
                                }
                            }
                        }
                    };

                if let Some(b) = b {
                    let iter = self.gather_attr_vars_created_since(b);

                    let var_list_addr = Addr::HeapCell(self.heap.to_list(iter));
                    let list_addr = self[temp_v!(2)];

                    self.unify(var_list_addr, list_addr);
                }
            }
            &SystemClauseType::GetContinuationChunk => {
                let e = self.store(self.deref(self[temp_v!(1)]));

                let e = if let Addr::Usize(e) = e {
                    e
                } else {
                    self.fail = true;
                    return Ok(());
                };

                let p_functor = self.store(self.deref(self[temp_v!(2)]));
                let p = self.heap.to_local_code_ptr(&p_functor).unwrap();

                let num_cells =
                    match code_repo.lookup_instr(self.last_call, &CodePtr::Local(p)) {
                        Some(line) => {
                            let perm_vars = match line.as_ref() {
                                Line::Control(ref ctrl_instr) => ctrl_instr.perm_vars(),
                                _ => None
                            };

                            perm_vars.unwrap()
                        }
                        _ => unreachable!()
                    };

                let mut addrs = vec![];

                for index in 1 .. num_cells + 1 {
                    addrs.push(self.stack.index_and_frame(e)[index]);
                }

                let chunk = Addr::HeapCell(self.heap.h());

                self.heap.push(HeapCellValue::NamedStr(
                    1 + num_cells,
                    clause_name!("cont_chunk"),
                    None,
                ));

                self.heap.push(HeapCellValue::Addr(p_functor));
                self.heap.extend(addrs.into_iter().map(HeapCellValue::Addr));

                self.unify(self[temp_v!(3)], chunk);
            }
            &SystemClauseType::GetLiftedHeapFromOffsetDiff => {
                let lh_offset = self[temp_v!(1)];

                match self.store(self.deref(lh_offset)) {
                    Addr::Usize(lh_offset) => {
                        if lh_offset >= self.lifted_heap.h() {
                            let solutions = self[temp_v!(2)];
                            let diff = self[temp_v!(3)];

                            self.unify(solutions, Addr::EmptyList);
                            self.unify(diff, Addr::EmptyList);
                        } else {
                            let h = self.heap.h();
                            let mut last_index = h;

                            for value in self.lifted_heap.iter_from(lh_offset) {
                                last_index = self.heap.h();

                                match value {
                                    HeapCellValue::Addr(ref addr) => {
                                        self.heap.push(HeapCellValue::Addr(*addr + h));
                                    }
                                    value => {
                                        self.heap.push(value.context_free_clone());
                                    }
                                }
                            }

                            if last_index < self.heap.h() {
                                let addr_opt =
                                    if let HeapCellValue::Addr(ref addr) = &self.heap[last_index] {
                                        Some(*addr)
                                    } else {
                                        None
                                    };

                                addr_opt.map(|addr| {
                                    let diff = self[temp_v!(3)];
                                    self.unify(diff, addr);
                                });
                            }

                            self.lifted_heap.truncate(lh_offset);

                            let solutions = self[temp_v!(2)];
                            self.unify(Addr::HeapCell(h), solutions);
                        }
                    }
                    _ => {
                        self.fail = true;
                    }
                }
            }
            &SystemClauseType::GetLiftedHeapFromOffset => {
                let lh_offset = self[temp_v!(1)];

                match self.store(self.deref(lh_offset)) {
                    Addr::Usize(lh_offset) => {
                        if lh_offset >= self.lifted_heap.h() {
                            let solutions = self[temp_v!(2)];
                            self.unify(solutions, Addr::EmptyList);
                        } else {
                            let h = self.heap.h();

                            for addr in self.lifted_heap.iter_from(lh_offset) {
                                match addr {
                                    HeapCellValue::Addr(ref addr) => {
                                        self.heap.push(HeapCellValue::Addr(*addr + h));
                                    }
                                    value => {
                                        self.heap.push(value.context_free_clone());
                                    }
                                }
                            }

                            self.lifted_heap.truncate(lh_offset);

                            let solutions = self[temp_v!(2)];
                            self.unify(Addr::HeapCell(h), solutions);
                        }
                    }
                    _ => {
                        self.fail = true;
                    }
                }
            }
            &SystemClauseType::GetDoubleQuotes => {
                let a1 = self[temp_v!(1)];

                match self.flags.double_quotes {
                    DoubleQuotes::Chars => {
                        let atom = self.heap.to_unifiable(
                            HeapCellValue::Atom(clause_name!("chars"), None)
                        );

                        self.unify(a1, atom);
                    }
                    DoubleQuotes::Atom  => {
                        let atom = self.heap.to_unifiable(
                            HeapCellValue::Atom(clause_name!("atom"), None)
                        );

                        self.unify(a1, atom);
                    }
                    DoubleQuotes::Codes => {
                        let atom = self.heap.to_unifiable(
                            HeapCellValue::Atom(clause_name!("codes"), None)
                        );

                        self.unify(a1, atom);
                    }
                }
            }
            &SystemClauseType::GetSCCCleaner => {
                let dest = self[temp_v!(1)];

                match cut_policy.downcast_mut::<SCCCutPolicy>().ok() {
                    Some(sgc_policy) => {
                        if let Some((addr, b_cutoff, prev_b)) = sgc_policy.pop_cont_pt() {
                            let b = self.stack.index_or_frame(self.b).prelude.b;

                            if b <= b_cutoff {
                                self.block = prev_b;

                                if let Some(r) = dest.as_var() {
                                    self.bind(r, addr);
                                    return return_from_clause!(self.last_call, self);
                                }
                            } else {
                                sgc_policy.push_cont_pt(addr, b_cutoff, prev_b);
                            }
                        }
                    }
                    None => {
                    }
                };

                self.fail = true;
            }
            &SystemClauseType::Halt => {
                std::process::exit(0);
            }
            &SystemClauseType::InstallSCCCleaner => {
                let addr = self[temp_v!(1)];
                let b = self.b;
                let prev_block = self.block;

                if cut_policy.downcast_ref::<SCCCutPolicy>().is_err() {
                    let (r_c_w_h, r_c_wo_h) = indices.get_cleaner_sites();
                    *cut_policy = Box::new(SCCCutPolicy::new(r_c_w_h, r_c_wo_h));
                }

                match cut_policy.downcast_mut::<SCCCutPolicy>().ok() {
                    Some(cut_policy) => {
                        self.install_new_block(temp_v!(2));
                        cut_policy.push_cont_pt(addr, b, prev_block);
                    }
                    None => panic!(
                        "install_cleaner: should have installed \\
                         SCCCutPolicy."
                    ),
                };
            }
            &SystemClauseType::InstallInferenceCounter => {
                // A1 = B, A2 = L
                let a1 = self.store(self.deref(self[temp_v!(1)]));
                let a2 = self.store(self.deref(self[temp_v!(2)]));

                if call_policy.downcast_ref::<CWILCallPolicy>().is_err() {
                    CWILCallPolicy::new_in_place(call_policy);
                }

                let n =
                    match Number::try_from((a2, &self.heap)) {
                        Ok(Number::Integer(n)) => {
                            Integer::from(&*n.clone())
                        }
                        Ok(Number::Fixnum(n)) => {
                            Integer::from(n)
                        }
                        _ => {
                            let stub = MachineError::functor_stub(
                                clause_name!("call_with_inference_limit"),
                                3,
                            );

                            return Err(self.error_form(
                                MachineError::type_error(
                                    self.heap.h(),
                                    ValidType::Integer,
                                    a2,
                                ),
                                stub,
                            ));
                        }
                    };

                match a1 {
                    Addr::Usize(bp) | Addr::CutPoint(bp) => {
                        match call_policy.downcast_mut::<CWILCallPolicy>().ok() {
                            Some(call_policy) => {
                                let count = call_policy.add_limit(n, bp).clone();
                                let count = self.heap.to_unifiable(
                                    HeapCellValue::Integer(Rc::new(count))
                                );

                                let a3 = self[temp_v!(3)];
                                self.unify(a3, count);
                            }
                            None => {
                                panic!(
                                    "install_inference_counter: should have installed \\
                                     CWILCallPolicy."
                                )
                            }
                        }
                    }
                    _ => {
                        unreachable!();
                    }
                }
            }
            &SystemClauseType::ModuleExists => {
                let module = self.store(self.deref(self[temp_v!(1)]));

                match module {
                    Addr::Con(h) => {
	                if let HeapCellValue::Atom(ref name, _) = &self.heap[h] {
                            self.fail = !indices.modules.contains_key(name);
                        } else {
                            unreachable!()
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                };
            }
            &SystemClauseType::ModuleOf => {
                let module = self.store(self.deref(self[temp_v!(2)]));

                match module {
                    Addr::Con(h) if self.heap.atom_at(h) => {
	                if let HeapCellValue::Atom(name, _) = self.heap.clone(h) {
                            let module = self.heap.to_unifiable(
                                HeapCellValue::Atom(
                                    name.owning_module(),
                                    None
                                ),
                            );

                            let target = self[temp_v!(1)];

                            self.unify(target, module);
                        } else {
                            unreachable!()
                        }
                    }
                    Addr::Str(s) => match self.heap.clone(s) {
                        HeapCellValue::NamedStr(_, name, ..) => {
                            let module = self.heap.to_unifiable(
                                HeapCellValue::Atom(
                                    name.owning_module(),
                                    None
                                ),
                            );

                            let target = self[temp_v!(1)];

                            self.unify(target, module);
                        }
                        HeapCellValue::Addr(addr) if addr.is_ref() => {
                            let err = MachineError::uninstantiation_error(addr);
                            let stub = MachineError::functor_stub(
                                clause_name!("$module_of"),
                                2,
                            );

                            return Err(self.error_form(err, stub));
                        }
                        _ => {
                            unreachable!()
                        }
                    },
                    _ => {
                        self.fail = true;
                    }
                };
            }
            &SystemClauseType::NoSuchPredicate => {
                let head = self[temp_v!(1)];

                self.fail = match self.store(self.deref(head)) {
                    Addr::Str(s) => match &self.heap[s] {
                        &HeapCellValue::NamedStr(arity, ref name, ref spec) => {
                            let module = name.owning_module();
                            indices.predicate_exists(name.clone(), module, arity, spec.clone())
                        }
                        _ => {
                            unreachable!()
                        }
                    },
                    Addr::Con(h) if self.heap.atom_at(h) => {
	                if let &HeapCellValue::Atom(ref name, ref spec) = &self.heap[h] {
                            let module = name.owning_module();
                            let spec = fetch_atom_op_spec(name.clone(), spec.clone(), &indices.op_dir);

                            indices.predicate_exists(name.clone(), module, 0, spec)
                        } else {
                            unreachable!()
                        }
                    }
                    head => {
                        let err = MachineError::type_error(self.heap.h(), ValidType::Callable, head);
                        let stub = MachineError::functor_stub(clause_name!("clause"), 2);

                        return Err(self.error_form(err, stub));
                    }
                };
            }
            &SystemClauseType::RedoAttrVarBinding => {
                let var   = self.store(self.deref(self[temp_v!(1)]));
                let value = self.store(self.deref(self[temp_v!(2)]));

                match var {
                    Addr::AttrVar(h) => {
                        self.heap[h] = HeapCellValue::Addr(value);
                    }
                    _ => {
                        unreachable!()
                    }
                }
            }
            &SystemClauseType::ResetGlobalVarAtKey => {
                let key = self[temp_v!(1)];

                match self.store(self.deref(key)) {
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(ref key, _) = &self.heap[h] {
                            indices.global_variables.swap_remove(key);
                        } else {
                            unreachable!()
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                }
            }
            &SystemClauseType::ResetGlobalVarAtOffset => {
                let key = self[temp_v!(1)];

                let key = match self.store(self.deref(key)) {
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(ref key, _) = &self.heap[h] {
                            key.clone()
                        } else {
                            unreachable!()
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                };

                let value = self[temp_v!(2)];
                let mut ball = Ball::new();

                ball.boundary = self.heap.h();

                copy_term(
                    CopyBallTerm::new(&mut self.stack, &mut self.heap, &mut ball.stub),
                    value,
                    AttrVarPolicy::DeepCopy,
                );

                let offset = self[temp_v!(3)];

                match self.store(self.deref(offset)) {
                    Addr::Usize(offset) => {
                        indices.global_variables.insert(key, (ball, Some(offset)));
                    }
                    _ => {
                        indices.global_variables.insert(key, (ball, None));
                    }
                }
            },
            &SystemClauseType::ResetAttrVarState => {
                self.attr_var_init.reset();
            }
            &SystemClauseType::RemoveCallPolicyCheck => {
                let restore_default =
                    match call_policy.downcast_mut::<CWILCallPolicy>().ok() {
                        Some(call_policy) => {
                            let a1 = self.store(self.deref(self[temp_v!(1)]));

                            match a1 {
                                Addr::Usize(bp) | Addr::CutPoint(bp) => {
                                    if call_policy.is_empty() && bp == self.b {
                                        Some(call_policy.into_inner())
                                    } else {
                                        None
                                    }
                                }
                                _ => {
                                    panic!("remove_call_policy_check: expected Usize in A1.");
                                }
                            }
                        }
                        None => panic!(
                            "remove_call_policy_check: requires \\
                             CWILCallPolicy."
                        ),
                    };

                if let Some(new_policy) = restore_default {
                    *call_policy = new_policy;
                }
            }
            &SystemClauseType::RemoveInferenceCounter => {
                match call_policy.downcast_mut::<CWILCallPolicy>().ok() {
                    Some(call_policy) => {
                        let a1 = self.store(self.deref(self[temp_v!(1)]));

                        match a1 {
                            Addr::Usize(bp) | Addr::CutPoint(bp) => {
                                let count = call_policy.remove_limit(bp).clone();
                                let count = self.heap.to_unifiable(
                                    HeapCellValue::Integer(Rc::new(count)),
                                );

                                let a2 = self[temp_v!(2)];

                                self.unify(a2, count);
                            }
                            _ => {
                                panic!("remove_inference_counter: expected Usize in A1.");
                            }
                        }
                    }
                    None => panic!(
                        "remove_inference_counter: requires \\
                         CWILCallPolicy."
                    ),
                }
            }
            &SystemClauseType::REPL(repl_code_ptr) => {
                return self.repl_redirect(repl_code_ptr);
            }
            &SystemClauseType::ModuleRetractClause => {
                let p = self.cp;
                let trans_type = DynamicTransactionType::ModuleRetract;

                self.p = CodePtr::DynamicTransaction(trans_type, p);
                return Ok(());
            }
            &SystemClauseType::RetractClause => {
                let p = self.cp;
                let trans_type = DynamicTransactionType::Retract;

                self.p = CodePtr::DynamicTransaction(trans_type, p);
                return Ok(());
            }
            &SystemClauseType::ReturnFromVerifyAttr => {
                let e = self.e;
                let frame_len = self.stack.index_and_frame(e).prelude.univ_prelude.num_cells;

                for i in 1 .. frame_len - 1 {
                    self[RegType::Temp(i)] = self.stack.index_and_frame(e)[i];
                }

                if let &Addr::CutPoint(b0) = &self.stack.index_and_frame(e)[frame_len - 1] {
                    self.b0 = b0;
                }

                if let &Addr::Usize(num_of_args) = &self.stack.index_and_frame(e)[frame_len] {
                    self.num_of_args = num_of_args;
                }

                self.deallocate();
                self.p = CodePtr::Local(self.stack.index_and_frame(e).prelude.interrupt_cp);

                return Ok(());
            }
            &SystemClauseType::RestoreCutPolicy => {
                let restore_default =
                    if let Ok(cut_policy) = cut_policy.downcast_ref::<SCCCutPolicy>() {
                        cut_policy.out_of_cont_pts()
                    } else {
                        false
                    };

                if restore_default {
                    *cut_policy = Box::new(DefaultCutPolicy {});
                }
            }
            &SystemClauseType::SetCutPoint(r) => {
                if cut_policy.cut(self, r) {
                    return Ok(());
                }
            }
            &SystemClauseType::SetCutPointByDefault(r) => {
                deref_cut(self, r)
            }
            &SystemClauseType::SetInput => {
                let addr = self.store(self.deref(self[temp_v!(1)]));
                let stream = self.get_stream_or_alias(addr, indices, "set_input", 1)?;

                if !stream.is_input_stream() {
                    let stub = MachineError::functor_stub(
                        clause_name!("set_input"),
                        1,
                    );

                    let user_alias = self.heap.to_unifiable(
                        HeapCellValue::Atom(clause_name!("user"), None),
                    );

                    let err = MachineError::permission_error(
                        self.heap.h(),
                        Permission::InputStream,
                        "stream",
                        user_alias,
                    );

                    return Err(self.error_form(err, stub));
                }

                *current_input_stream = stream;
            }
            &SystemClauseType::SetOutput => {
                let addr = self.store(self.deref(self[temp_v!(1)]));
                let stream = self.get_stream_or_alias(addr, indices, "set_output", 1)?;

                if !stream.is_output_stream() {
                    let stub = MachineError::functor_stub(
                        clause_name!("set_input"),
                        1,
                    );

                    let user_alias = self.heap.to_unifiable(
                        HeapCellValue::Atom(clause_name!("user"), None),
                    );

                    let err = MachineError::permission_error(
                        self.heap.h(),
                        Permission::OutputStream,
                        "stream",
                        user_alias,
                    );

                    return Err(self.error_form(err, stub));
                }

                *current_output_stream = stream;
            }
            &SystemClauseType::SetDoubleQuotes => {
                match self[temp_v!(1)] {
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(ref atom, _) = &self.heap[h] {
                            self.flags.double_quotes =
                                match atom.as_str() {
                                    "atom"  => DoubleQuotes::Atom,
                                    "chars" => DoubleQuotes::Chars,
                                    "codes" => DoubleQuotes::Codes,
                                    _ => {
                                        self.fail = true;
                                        return Ok(());
                                    }
                                };
                        } else {
                            unreachable!()
                        }
                    }
                    _ => {
                        self.fail = true;
                    }
                }
            }
            &SystemClauseType::InferenceLevel => {
                let a1 = self[temp_v!(1)];
                let a2 = self.store(self.deref(self[temp_v!(2)]));

                match a2 {
                    Addr::CutPoint(bp) | Addr::Usize(bp) => {
                        let prev_b = self.stack.index_or_frame(self.b).prelude.b;

                        if prev_b <= bp {
                            let a2 = self.heap.to_unifiable(
                                HeapCellValue::Atom(clause_name!("!"), None)
                            );

                            self.unify(a1, a2);
                        } else {
                            let a2 = self.heap.to_unifiable(
                                HeapCellValue::Atom(clause_name!("true"), None)
                            );

                            self.unify(a1, a2);
                        }
                    }
                    _ => {
                        self.fail = true;
                    }
                }
            }
            &SystemClauseType::CleanUpBlock => {
                let nb = self.store(self.deref(self[temp_v!(1)]));

                match nb {
                    Addr::Usize(nb) => {
                        let b = self.b;

                        if nb > 0 && self.stack.index_or_frame(b).prelude.b == nb {
                            self.b = self.stack.index_or_frame(nb).prelude.b;
                        }
                    }
                    _ => {
                        self.fail = true;
                    }
                };
            }
            &SystemClauseType::EraseBall => {
                self.ball.reset();
            }
            &SystemClauseType::Fail => {
                self.fail = true;
            }
            &SystemClauseType::GetBall => {
                let addr = self.store(self.deref(self[temp_v!(1)]));
                let h = self.heap.h();

                if self.ball.stub.h() > 0 {
                    let stub = self.ball.copy_and_align(h);
                    self.heap.extend(stub.into_iter());
                } else {
                    self.fail = true;
                    return Ok(());
                }

                let ball = self.heap[h].as_addr(h);

                match addr.as_var() {
                    Some(r) => self.bind(r, ball),
                    _ => self.fail = true,
                };
            }
            &SystemClauseType::GetCurrentBlock => {
                let c = Constant::Usize(self.block);
                let addr = self[temp_v!(1)];

                self.write_constant_to_var(addr, &c);
            }
            &SystemClauseType::GetBValue => {
                let a1 = self[temp_v!(1)];
                let a2 = Addr::Usize(self.b);

                self.unify(a1, a2);
            }
            &SystemClauseType::GetClause => {
                let head = self[temp_v!(1)];

                let subsection = match self.store(self.deref(head)) {
                    Addr::Str(s) => match &self.heap[s] {
                        &HeapCellValue::NamedStr(arity, ref name, ..) => {
                            indices.get_clause_subsection(
                                name.owning_module(),
                                name.clone(),
                                arity,
                            )
                        }
                        _ => {
                            unreachable!()
                        }
                    },
                    Addr::Con(h) if self.heap.atom_at(h) => {
	                if let &HeapCellValue::Atom(ref name, _) = &self.heap[h] {
                            indices.get_clause_subsection(
                                name.owning_module(),
                                name.clone(),
                                0,
                            )
                        } else {
                            unreachable!()
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                };

                match subsection {
                    Some(dynamic_predicate_info) => {
                        self.execute_at_index(
                            2,
                            dir_entry!(dynamic_predicate_info.clauses_subsection_p),
                        );

                        return Ok(());
                    }
                    _ => {
                        unreachable!()
                    }
                }
            }
            &SystemClauseType::GetCutPoint => {
                let a1 = self[temp_v!(1)];
                let a2 = Addr::CutPoint(self.b0);

                self.unify(a1, a2);
            }
            &SystemClauseType::InstallNewBlock => {
                self.install_new_block(temp_v!(1));
            }
            &SystemClauseType::NextEP => {
                let first_arg = self.store(self.deref(self[temp_v!(1)]));

                match first_arg {
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(ref name, _) = self.heap.clone(h) {
                            if name.as_str() == "first" {
                                if self.e == 0 {
                                    self.fail = true;
                                    return Ok(());
                                }

                                let cp = (self.stack.index_and_frame(self.e).prelude.cp - 1).unwrap();

                                let e = self.stack.index_and_frame(self.e).prelude.e;
                                let e = Addr::Usize(e);

                                let p = cp.as_functor(&mut self.heap);

                                self.unify(self[temp_v!(2)], e);

                                if !self.fail {
                                    self.unify(self[temp_v!(3)], p);
                                }
                            } else {
                                unreachable!()
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    Addr::Usize(e) => {
                        if e == 0 {
                            self.fail = true;
                            return Ok(());
                        }

                        // get the call site so that the number of active permanent variables can be read
                        // from it later.
                        let cp = (self.stack.index_and_frame(e).prelude.cp - 1).unwrap();

                        let p = cp.as_functor(&mut self.heap);
                        let e = self.stack.index_and_frame(e).prelude.e;

                        let e = Addr::Usize(e);

                        self.unify(self[temp_v!(2)], e);

                        if !self.fail {
                            self.unify(self[temp_v!(3)], p);
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                }
            }
            &SystemClauseType::PointsToContinuationResetMarker => {
                let addr = self.store(self.deref(self[temp_v!(1)]));

                let p = match self.heap.to_local_code_ptr(&addr) {
                    Some(p) => {
                        p + 1
                    }
                    None => {
                        self.fail = true;
                        return Ok(());
                    }
                };

                if p.is_reset_cont_marker(code_repo, self.last_call) {
                    return return_from_clause!(self.last_call, self);
                }

                self.fail = true;
                return Ok(());
            }
            &SystemClauseType::QuotedToken => {
                let addr = self.store(self.deref(self[temp_v!(1)]));

                match addr {
                    Addr::Fixnum(n) => {
                        let n = u32::try_from(n).ok();
                        let n = n.and_then(std::char::from_u32);

                        self.fail = match n {
                            Some(c) => {
                                non_quoted_token(once(c))
                            }
                            None => {
                                true
                            }
                        };
                    }
                    Addr::Char(c) => {
                        self.fail = non_quoted_token(once(c));
                    }
                    Addr::Con(h) => {
	                    if let HeapCellValue::Atom(atom, _) = &self.heap[h] {
                            self.fail = non_quoted_token(atom.as_str().chars());
                        }
                    }
                    _ => {
                        self.fail = true;
                    }
                }
            }
            &SystemClauseType::ReadQueryTerm => {
                current_input_stream.reset();

                readline::set_prompt(true);
                let result = self.read_term(current_input_stream.clone(), indices);
                readline::set_prompt(false);

                match result {
                    Ok(()) => {
                    }
                    Err(e) => {
                        *current_input_stream = readline::input_stream();
                        return Err(e);
                    }
                }
            }
            &SystemClauseType::ReadTerm => {
                readline::set_prompt(false);

                let stream = self.get_stream_or_alias(
                    self[temp_v!(1)],
                    indices,
                    "read_term",
                    3,
                )?;

                self.read_term(stream, indices)?;
            }
            &SystemClauseType::ReadTermFromChars => {
                let mut heap_pstr_iter = self.heap_pstr_iter(self[temp_v!(1)]);
                let chars = heap_pstr_iter.to_string();

                let mut stream = self.open_parsing_stream(
                    Stream::from(chars),
                    "read_term_from_chars",
                    2,
                )?;

                if let Addr::EmptyList = heap_pstr_iter.focus() {
                    let term_write_result =
                        match self.read(
                            &mut stream,
                            indices.atom_tbl.clone(),
                            &indices.op_dir,
                        ) {
                            Ok(term_write_result) => {
                                term_write_result
                            }
                            Err(e) => {
                                let stub = MachineError::functor_stub(
                                    clause_name!("read_term_from_chars"),
                                    2,
                                );

                                let h = self.heap.h();
                                let e = MachineError::session_error(h, SessionError::from(e));

                                return Err(self.error_form(e, stub));
                            }
                        };

                    let result = Addr::HeapCell(term_write_result.heap_loc);

                    if let Some(var) = self.store(self.deref(self[temp_v!(2)])).as_var() {
                        self.bind(var, result);
                    } else {
                        unreachable!()
                    }
                } else {
                    unreachable!()
                }
            }
            &SystemClauseType::ResetBlock => {
                let addr = self.deref(self[temp_v!(1)]);
                self.reset_block(addr);
            }
            &SystemClauseType::ResetContinuationMarker => {
                self[temp_v!(3)] = self.heap.to_unifiable(
                    HeapCellValue::Atom(clause_name!("none"), None)
                );

                let h = self.heap.h();

                self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
                self[temp_v!(4)] = Addr::HeapCell(h);
            }
            &SystemClauseType::SetBall => {
                self.set_ball();
            }
            &SystemClauseType::SetSeed => {
                let seed = self.store(self.deref(self[temp_v!(1)]));

                let seed =
                    match Number::try_from((seed, &self.heap)) {
                        Ok(Number::Fixnum(n)) => {
                            Integer::from(n)
                        }
                        Ok(Number::Integer(n)) => {
                            Integer::from(n.as_ref())
                        }
                        Ok(Number::Rational(n))
                            if n.denom() == &1 => {
                                n.numer().clone()
                            }
                        _ => {
                            self.fail = true;
                            return Ok(());
                        }
                    };

                let mut rand = RANDOM_STATE.borrow_mut();
                rand.seed(&seed);
            }
            &SystemClauseType::SkipMaxList =>
                if let Err(err) = self.skip_max_list() {
                    return Err(err);
                },
            &SystemClauseType::Sleep => {
                let time = self.store(self.deref(self[temp_v!(1)]));

                let time = match Number::try_from((time, &self.heap)) {
                    Ok(Number::Float(OrderedFloat(n))) => n,
                    Ok(Number::Fixnum(n)) => n as f64,
                    Ok(Number::Integer(n)) => n.to_f64(),
                    _ => {
                        unreachable!()
                    }
                };

                let duration = Duration::new(1, 0);
                let duration = duration.mul_f64(time);
                ::std::thread::sleep(duration);
            }
            &SystemClauseType::SocketClientOpen => {
                let addr = self.store(self.deref(self[temp_v!(1)]));
                let port = self.store(self.deref(self[temp_v!(2)]));

                let socket_atom =
                    match addr {
                        Addr::Con(h) if self.heap.atom_at(h) => {
                            if let HeapCellValue::Atom(ref name, _) = &self.heap[h] {
                                name.clone()
                            } else {
                                unreachable!()
                            }
                        }
                        _ => {
                            unreachable!()
                        }
                    };

                let port =
                    match port {
                        Addr::Fixnum(n) => {
                            n.to_string()
                        }
                        Addr::Usize(n) => {
                            n.to_string()
                        }
                        Addr::Con(h) => {
                            match &self.heap[h] {
                                HeapCellValue::Atom(ref name, _) => {
                                    name.as_str().to_string()
                                }
                                HeapCellValue::Integer(ref n) => {
                                    n.to_string()
                                }
                                _ => {
                                    unreachable!()
                                }
                            }
                        }
                        _ => {
                            unreachable!()
                        }
                    };

                let socket_addr =
                    format!(
                        "{}:{}",
                        if socket_atom.as_str() == "" {
                            "127.0.0.1"
                        } else {
                            socket_atom.as_str()
                        },
                        port,
                    );

                let alias = self[temp_v!(4)];
                let eof_action = self[temp_v!(5)];
                let reposition = self[temp_v!(6)];
                let stream_type = self[temp_v!(7)];

                let options =
                    self.to_stream_options(alias, eof_action, reposition, stream_type);

                if options.reposition {
                    return Err(self.reposition_error("socket_client_open", 3));
                }

                if let Some(ref alias) = &options.alias {
                    if indices.stream_aliases.contains_key(alias) {
                        return Err(self.occupied_alias_permission_error(
                            alias.clone(),
                            "socket_client_open",
                            3,
                        ));
                    }
                }

                let stream =
                    match TcpStream::connect(&socket_addr).map_err(|e| e.kind()) {
                        Ok(tcp_stream) => {
                            let socket_addr = clause_name!(socket_addr, indices.atom_tbl.clone());

                            let mut stream = Stream::from_tcp_stream(socket_addr, tcp_stream);
                            stream.options = options;

                            if let Some(ref alias) = &stream.options.alias {
                                indices.stream_aliases.insert(alias.clone(), stream.clone());
                            }

                            indices.streams.insert(stream.clone());

                            self.heap.to_unifiable(HeapCellValue::Stream(stream))
                        }
                        Err(ErrorKind::PermissionDenied) => {
                            return Err(self.open_permission_error(addr, "socket_client_open", 3));
                        }
                        Err(ErrorKind::NotFound) => {
                            let stub = MachineError::functor_stub(
                                clause_name!("socket_client_open"),
                                3,
                            );

                            let err = MachineError::existence_error(
                                self.heap.h(),
                                ExistenceError::SourceSink(addr),
                            );

                            return Err(self.error_form(err, stub));
                        }
                        Err(_) => {
                            // for now, just fail. expand to meaningful error messages later.
                            self.fail = true;
                            return Ok(());
                        }
                    };

                let stream_addr = self.store(self.deref(self[temp_v!(3)]));
                self.bind(stream_addr.as_var().unwrap(), stream);
            }
            &SystemClauseType::SocketServerOpen => {
                let addr = self.store(self.deref(self[temp_v!(1)]));
                let socket_atom =
                    match addr {
                        Addr::EmptyList => {
                            "127.0.0.1".to_string()
                        }
                        Addr::Con(h) if self.heap.atom_at(h) => {
                            match &self.heap[h] {
                                HeapCellValue::Atom(ref name, _) => {
                                    name.as_str().to_string()
                                }
                                _ => {
                                    unreachable!()
                                }
                            }
                        }
                        _ => {
                            unreachable!()
                        }
                    };

                let port =
                    match self.store(self.deref(self[temp_v!(2)])) {
                        Addr::Fixnum(n) => {
                            n.to_string()
                        }
                        Addr::Usize(n) => {
                            n.to_string()
                        }
                        Addr::Con(h) => {
                            match &self.heap[h] {
                                HeapCellValue::Integer(ref n) => {
                                    n.to_string()
                                }
                                _ => {
                                    unreachable!()
                                }
                            }
                        }
                        addr if addr.is_ref() => {
                            "0".to_string()
                        }
                        _ => {
                            unreachable!()
                        }
                    };

                let had_zero_port = &port == "0";

                let server_addr = if socket_atom.is_empty() {
                    port
                } else {
                    format!("{}:{}", socket_atom, port)
                };

                let (tcp_listener, port) =
                    match TcpListener::bind(server_addr).map_err(|e| e.kind()) {
                        Ok(tcp_listener) => {
                            let port = tcp_listener.local_addr().map(|addr| addr.port()).ok();

                            if let Some(port) = port {
                                (
                                    self.heap.to_unifiable(HeapCellValue::TcpListener(tcp_listener)),
                                    port as usize,
                                )
                            } else {
                                self.fail = true;
                                return Ok(());
                            }
                        }
                        Err(ErrorKind::PermissionDenied) => {
                            return Err(self.open_permission_error(addr, "socket_server_open", 2));
                        }
                        _ => {
                            self.fail = true;
                            return Ok(());
                        }
                    };

                let addr = self.store(self.deref(self[temp_v!(3)]));
                self.bind(addr.as_var().unwrap(), tcp_listener);

                if had_zero_port {
                    self.unify(self[temp_v!(2)], Addr::Usize(port));
                }
            }
            &SystemClauseType::SocketServerAccept => {
                let alias = self[temp_v!(4)];
                let eof_action = self[temp_v!(5)];
                let reposition = self[temp_v!(6)];
                let stream_type = self[temp_v!(7)];

                let options =
                    self.to_stream_options(alias, eof_action, reposition, stream_type);

                if options.reposition {
                    return Err(self.reposition_error("socket_server_accept", 4));
                }

                if let Some(ref alias) = &options.alias {
                    if indices.stream_aliases.contains_key(alias) {
                        return Err(self.occupied_alias_permission_error(
                            alias.clone(),
                            "socket_server_accept",
                            4,
                        ));
                    }
                }

                match self.store(self.deref(self[temp_v!(1)])) {
                    Addr::TcpListener(h) => {
                        match &mut self.heap[h] {
                            HeapCellValue::TcpListener(ref mut tcp_listener) => {
                                match tcp_listener.accept().ok() {
                                    Some((tcp_stream, socket_addr)) => {
                                        let client =
                                            clause_name!(format!("{}", socket_addr), indices.atom_tbl);

                                        let mut tcp_stream =
                                            Stream::from_tcp_stream(client.clone(), tcp_stream);

                                        tcp_stream.options = options;

                                        if let Some(ref alias) = &tcp_stream.options.alias {
                                            indices.stream_aliases.insert(
                                                alias.clone(),
                                                tcp_stream.clone(),
                                            );
                                        }

                                        indices.streams.insert(tcp_stream.clone());

                                        let tcp_stream =
                                            self.heap.to_unifiable(HeapCellValue::Stream(tcp_stream));

                                        let client =
                                            self.heap.to_unifiable(HeapCellValue::Atom(client, None));

                                        let client_addr = self.store(self.deref(self[temp_v!(2)]));
                                        let stream_addr = self.store(self.deref(self[temp_v!(3)]));

                                        self.bind(client_addr.as_var().unwrap(), client);
                                        self.bind(stream_addr.as_var().unwrap(), tcp_stream);
                                    }
                                    None => {
                                        self.fail = true;
                                        return Ok(());
                                    }
                                }
                            }
                            culprit => {
                                let culprit = culprit.as_addr(h);

                                return Err(self.type_error(
                                    ValidType::TcpListener,
                                    culprit,
                                    clause_name!("socket_server_accept"),
                                    4,
                                ));
                            }
                        }
                    }
                    culprit => {
                        return Err(self.type_error(
                            ValidType::TcpListener,
                            culprit,
                            clause_name!("socket_server_accept"),
                            4,
                        ));
                    }
                }
            }
            &SystemClauseType::SocketServerClose => {
                match self.store(self.deref(self[temp_v!(1)])) {
                    Addr::TcpListener(h) => {
                        let closed_tcp_listener = clause_name!("$closed_tcp_listener");
                        self.heap[h] = HeapCellValue::Atom(closed_tcp_listener, None);
                    }
                    culprit => {
                        return Err(self.type_error(
                            ValidType::TcpListener,
                            culprit,
                            clause_name!("socket_server_close"),
                            1,
                        ));
                    }
                }
            }
            &SystemClauseType::SetStreamPosition => {
                let mut stream = self.get_stream_or_alias(
                    self[temp_v!(1)],
                    indices,
                    "set_stream_position",
                    2,
                )?;

                if !stream.options.reposition {
                    let stub = MachineError::functor_stub(clause_name!("set_stream_position"), 2);

                    let err = MachineError::permission_error(
                        self.heap.h(),
                        Permission::Reposition,
                        "stream",
                        vec![HeapCellValue::Stream(stream)],
                    );

                    return Err(self.error_form(err, stub));
                }

                let position = self.store(self.deref(self[temp_v!(2)]));

                let position =
                    match Number::try_from((position, &self.heap)) {
                        Ok(Number::Fixnum(n)) => {
                            n as u64
                        }
                        Ok(Number::Integer(n)) => {
                            if let Some(n) = n.to_u64() {
                                n
                            } else {
                                self.fail = true;
                                return Ok(());
                            }
                        }
                        _ => {
                            unreachable!()
                        }
                    };

                stream.set_position(position);
            }
            &SystemClauseType::StreamProperty => {
                let mut stream = self.get_stream_or_alias(
                    self[temp_v!(1)],
                    indices,
                    "stream_property",
                    2,
                )?;

                let property =
                    match self.store(self.deref(self[temp_v!(2)])) {
                        Addr::Con(h) if self.heap.atom_at(h) => {
                            match &self.heap[h] {
                                HeapCellValue::Atom(ref name, _) => {
                                    match name.as_str() {
                                        "file_name" => {
                                            if let Some(file_name) = stream.file_name() {
                                                HeapCellValue::Atom(
                                                    file_name,
                                                    None,
                                                )
                                            } else {
                                                self.fail = true;
                                                return Ok(());
                                            }
                                        }
                                        "mode" => {
                                            HeapCellValue::Atom(
                                                clause_name!(stream.mode()),
                                                None,
                                            )
                                        }
                                        "direction" => {
                                            HeapCellValue::Atom(
                                                if stream.is_input_stream() && stream.is_output_stream() {
                                                    clause_name!("input_output")
                                                } else if stream.is_input_stream() {
                                                    clause_name!("input")
                                                } else {
                                                    clause_name!("output")
                                                },
                                                None,
                                            )
                                        }
                                        "alias" => {
                                            if let Some(alias) = &stream.options.alias {
                                                HeapCellValue::Atom(
                                                    alias.clone(),
                                                    None,
                                                )
                                            } else {
                                                self.fail = true;
                                                return Ok(());
                                            }
                                        }
                                        "position" => {
                                            if let Some(position) = stream.position() {
                                                HeapCellValue::Addr(Addr::Usize(position as usize))
                                            } else {
                                                self.fail = true;
                                                return Ok(());
                                            }
                                        }
                                        "end_of_stream" => {
                                            let end_of_stream_pos = stream.position_relative_to_end();

                                            HeapCellValue::Atom(
                                                clause_name!(end_of_stream_pos.as_str()),
                                                None,
                                            )
                                        }
                                        "eof_action" => {
                                            HeapCellValue::Atom(
                                                clause_name!(stream.options.eof_action.as_str()),
                                                None,
                                            )
                                        }
                                        "reposition" => {
                                            HeapCellValue::Atom(
                                                clause_name!(if stream.options.reposition {
                                                    "true"
                                                } else {
                                                    "false"
                                                }),
                                                None,
                                            )
                                        }
                                        "type" => {
                                            HeapCellValue::Atom(
                                                clause_name!(stream.options.stream_type.as_property_str()),
                                                None,
                                            )
                                        }
                                        _ => {
                                            unreachable!()
                                        }
                                    }
                                }
                                _ => {
                                    unreachable!()
                                }
                            }
                        }
                        _ => {
                            unreachable!()
                        }
                    };

                let property = self.heap.to_unifiable(property);
                self.unify(self[temp_v!(3)], property);
            }
            &SystemClauseType::StoreGlobalVar => {
                let key = self[temp_v!(1)];

                let key = match self.store(self.deref(key)) {
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(ref atom, _) = &self.heap[h] {
                            atom.clone()
                        } else {
                            unreachable!()
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                };

                let value = self[temp_v!(2)];
                let mut ball = Ball::new();

                ball.boundary = self.heap.h();

                copy_term(
                    CopyBallTerm::new(&mut self.stack, &mut self.heap, &mut ball.stub),
                    value,
                    AttrVarPolicy::DeepCopy,
                );

                indices.global_variables.insert(key, (ball, None));
            }
            &SystemClauseType::StoreGlobalVarWithOffset => {
                let key = self[temp_v!(1)];

                let key = match self.store(self.deref(key)) {
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(ref atom, _) = &self.heap[h] {
                            atom.clone()
                        } else {
                            unreachable!()
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                };

                let value = self[temp_v!(2)];
                let mut ball = Ball::new();
                let h = self.heap.h();

                ball.boundary = h;

                copy_term(
                    CopyBallTerm::new(&mut self.stack, &mut self.heap, &mut ball.stub),
                    value.clone(),
                    AttrVarPolicy::DeepCopy,
                );

                let stub = ball.copy_and_align(h);
                self.heap.extend(stub.into_iter());

                indices.global_variables.insert(key, (ball, Some(h)));

                self.unify(value, Addr::HeapCell(h));
            }
            &SystemClauseType::Succeed => {
            }
            &SystemClauseType::TermAttributedVariables => {
                let seen_vars = self.attr_vars_of_term(self[temp_v!(1)]);
                let outcome = Addr::HeapCell(self.heap.to_list(seen_vars.into_iter()));

                self.unify(self[temp_v!(2)], outcome);
            }
            &SystemClauseType::TermVariables => {
                let a1 = self[temp_v!(1)];
                let mut seen_set  = IndexSet::new();
                let mut seen_vars = vec![];

                for addr in self.acyclic_pre_order_iter(a1) {
                    if addr.is_ref() && !seen_set.contains(&addr) {
                        seen_vars.push(addr);
                        seen_set.insert(addr);
                    }
                }

                let outcome = Addr::HeapCell(self.heap.to_list(seen_vars.into_iter()));
                self.unify(self[temp_v!(2)], outcome);
            }
            &SystemClauseType::TruncateLiftedHeapTo => {
                match self.store(self.deref(self[temp_v!(1)])) {
                    Addr::Usize(lh_offset) =>
                        self.lifted_heap.truncate(lh_offset),
                    _ =>
                        self.fail = true,
                }
            }
            &SystemClauseType::UnifyWithOccursCheck => {
                let a1 = self[temp_v!(1)];
                let a2 = self[temp_v!(2)];

                self.unify_with_occurs_check(a1, a2);
            }
            &SystemClauseType::UnwindEnvironments => {
                let mut e = self.e;
                let mut cp = self.cp;

                while e > 0 {
                    if cp.is_reset_cont_marker(code_repo, self.last_call) {
                        self.e = e;
                        self.p = CodePtr::Local(cp + 1); // skip the reset marker.

                        return Ok(());
                    }

                    cp = self.stack.index_and_frame(e).prelude.cp;
                    e = self.stack.index_and_frame(e).prelude.e;
                }
            }
            &SystemClauseType::UnwindStack => {
                self.unwind_stack();
            }
            &SystemClauseType::Variant => {
                self.fail = self.structural_eq_test();
            }
            &SystemClauseType::WAMInstructions => {
                let name  = self[temp_v!(1)];
                let arity = self[temp_v!(2)];

                let name = match self.store(self.deref(name)) {
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(ref atom, _) = &self.heap[h] {
                            atom.clone()
                        } else {
                            unreachable!()
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                };

                let arity = self.store(self.deref(arity));

                let arity =
                    match Number::try_from((arity, &self.heap)) {
                        Ok(Number::Fixnum(n)) => {
                            Integer::from(n)
                        }
                        Ok(Number::Integer(n)) => {
                            Integer::from(n.as_ref())
                        }
                        _ => {
                            unreachable!()
                        }
                    };

                let first_idx = match indices
                    .code_dir
                    .get(&(name.clone(), arity.to_usize().unwrap()))
                {
                    Some(ref idx) if idx.local().is_some() => {
                        if let Some(idx) = idx.local() {
                            idx
                        } else {
                            unreachable!()
                        }
                    }
                    _ => {
                        let arity = arity.to_usize().unwrap();
                        let stub = MachineError::functor_stub(name.clone(), arity);
                        let h = self.heap.h();

                        let err = MachineError::existence_error(
                            h,
                            ExistenceError::Procedure(name, arity),
                        );

                        let err = self.error_form(err, stub);

                        self.throw_exception(err);
                        return Ok(());
                    }
                };

                let mut h = self.heap.h();
                let mut functors = vec![];

                walk_code(
                    &code_repo.code,
                    first_idx,
                    |instr| {
                        let section = instr.to_functor(h);
                        functors.push(Addr::HeapCell(h));

                        h += section.len();
                        self.heap.extend(section.into_iter());
                    },
                );

                let listing = Addr::HeapCell(self.heap.to_list(functors.into_iter()));
                let listing_var = self[temp_v!(3)];

                self.unify(listing, listing_var);
            }
            &SystemClauseType::WriteTerm => {
                let mut stream = self.get_stream_or_alias(
                    self[temp_v!(1)],
                    indices,
                    "write_term",
                    3,
                )?;

                self.check_stream_properties(
                    &mut stream,
                    StreamType::Text,
                    None, // input
                    clause_name!("write_term"),
                    3,
                )?;

                let opt_err =
                    if !stream.is_output_stream() {
                        Some("stream") // 8.14.2.3 g)
                    } else if stream.options.stream_type == StreamType::Binary {
                        Some("binary_stream") // 8.14.2.3 h)
                    } else {
                        None
                    };

                if let Some(err_string) = opt_err {
                    return Err(self.stream_permission_error(
                        Permission::OutputStream,
                        err_string,
                        stream,
                        clause_name!("write_term"),
                        3,
                    ));
                }

                let addr = self[temp_v!(2)];

                let printer =
                    match self.write_term(&indices.op_dir)? {
                        None => {
                            self.fail = true;
                            return Ok(());
                        }
                        Some(printer) => {
                            printer
                        }
                    };

                let output = printer.print(addr);

                match write!(&mut stream, "{}", output.result()) {
                    Ok(_) => {
                    }
                    Err(_) => {
                        let stub = MachineError::functor_stub(clause_name!("open"), 4);
                        let err = MachineError::existence_error(
                            self.heap.h(),
                            ExistenceError::Stream(self[temp_v!(1)]),
                        );

                        return Err(self.error_form(err, stub));
                    }
                }

                stream.flush().unwrap();
            }
            &SystemClauseType::WriteTermToChars => {
                let addr = self[temp_v!(2)];

                let printer =
                    match self.write_term(&indices.op_dir)? {
                        None => {
                            self.fail = true;
                            return Ok(());
                        }
                        Some(printer) => {
                            printer
                        }
                    };

                let result = printer.print(addr).result();
                let chars = self.heap.put_complete_string(&result);

                let result_addr = self.store(self.deref(self[temp_v!(1)]));

                if let Some(var) = result_addr.as_var() {
                    self.bind(var, chars);
                } else {
                    unreachable!()
                }
            }
            &SystemClauseType::ScryerPrologVersion => {
                use crate::git_version::git_version;
                let version = self[temp_v!(1)];
                let buffer =
                    git_version!(cargo_prefix = "cargo:", fallback = "unknown");
                let chars = buffer.chars().map(|c| Addr::Char(c));
                let result = Addr::HeapCell(self.heap.to_list(chars));
                self.unify(version, result);
            }
            &SystemClauseType::CryptoRandomByte => {
                let arg = self[temp_v!(1)];
                let mut bytes: [u8; 1] = [0];

                match rng().fill(&mut bytes) {
                    Ok(()) => {
                    }
                    Err(_) => {
                        // the error payload here is of type 'Unspecified',
                        // which contains no information whatsoever. So, for now,
                        // just fail.
                        self.fail = true;
                        return Ok(());
                    }
                }

                let byte = self.heap.to_unifiable(
                    HeapCellValue::Integer(Rc::new(Integer::from(bytes[0])))
                );

                self.unify(arg, byte);
            }
            &SystemClauseType::CryptoDataHash => {
                let stub = MachineError::functor_stub(clause_name!("crypto_data_hash"), 3);
                let bytes = self.integers_to_bytevec(temp_v!(1), stub);

                let algorithm = self[temp_v!(3)];
                let algorithm_str = match self.store(self.deref(algorithm)) {
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(ref atom, _) = &self.heap[h] {
                            atom.as_str()
                        } else {
                            unreachable!()
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                };

                let ints_list =
                        match algorithm_str  {
                          "sha3_224" =>   { let mut context = Sha3_224::new();
                                            context.input(&bytes);
                                            Addr::HeapCell(self.heap.to_list(context.result().as_ref().iter().map(|b| HeapCellValue::from(Addr::Fixnum(*b as isize))))) }
                          "sha3_256" =>   { let mut context = Sha3_256::new();
                                            context.input(&bytes);
                                            Addr::HeapCell(self.heap.to_list(context.result().as_ref().iter().map(|b| HeapCellValue::from(Addr::Fixnum(*b as isize))))) }
                          "sha3_384" =>   { let mut context = Sha3_384::new();
                                            context.input(&bytes);
                                            Addr::HeapCell(self.heap.to_list(context.result().as_ref().iter().map(|b| HeapCellValue::from(Addr::Fixnum(*b as isize))))) }
                          "sha3_512" =>   { let mut context = Sha3_512::new();
                                            context.input(&bytes);
                                            Addr::HeapCell(self.heap.to_list(context.result().as_ref().iter().map(|b| HeapCellValue::from(Addr::Fixnum(*b as isize))))) }
                          "blake2s256" => { let mut context = Blake2s::new();
                                            context.input(&bytes);
                                            Addr::HeapCell(self.heap.to_list(context.result().as_ref().iter().map(|b| HeapCellValue::from(Addr::Fixnum(*b as isize))))) }
                          "blake2b512" => { let mut context = Blake2b::new();
                                            context.input(&bytes);
                                            Addr::HeapCell(self.heap.to_list(context.result().as_ref().iter().map(|b| HeapCellValue::from(Addr::Fixnum(*b as isize))))) }
                          "ripemd160" =>  { let mut context = Ripemd160::new();
                                            context.input(&bytes);
                                            Addr::HeapCell(self.heap.to_list(context.result().as_ref().iter().map(|b| HeapCellValue::from(Addr::Fixnum(*b as isize))))) }
                          _ => { let ints = digest::digest(
                                                match algorithm_str {
                                                   "sha256" =>     { &digest::SHA256 }
                                                   "sha384" =>     { &digest::SHA384 }
                                                   "sha512" =>     { &digest::SHA512 }
                                                   "sha512_256" => { &digest::SHA512_256 }
                                                   _ =>            { unreachable!() }
                                                },
                                                &bytes);
                                 Addr::HeapCell(self.heap.to_list(ints.as_ref().iter().map(|b| HeapCellValue::from(Addr::Fixnum(*b as isize)))))
                               }
                        };

                self.unify(self[temp_v!(2)], ints_list);
            }
            &SystemClauseType::CryptoDataHKDF => {
                let stub1 = MachineError::functor_stub(clause_name!("crypto_data_hkdf"), 4);
                let data = self.integers_to_bytevec(temp_v!(1), stub1);
                let stub2 = MachineError::functor_stub(clause_name!("crypto_data_hkdf"), 4);
                let salt = self.integers_to_bytevec(temp_v!(2), stub2);
                let stub3 = MachineError::functor_stub(clause_name!("crypto_data_hkdf"), 4);
                let info = self.integers_to_bytevec(temp_v!(3), stub3);

                let algorithm = match self.store(self.deref(self[temp_v!(4)])) {
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(ref atom, _) = &self.heap[h] {
                            atom.as_str()
                        } else {
                            unreachable!()
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                };

                let length =
                    match Number::try_from((self[temp_v!(5)], &self.heap)) {
                        Ok(Number::Fixnum(n)) => {
                            usize::try_from(n).unwrap()
                        }
                        Ok(Number::Integer(n)) => {
                            match n.to_usize() {
                                Some(u) => { u }
                                _ => { self.fail = true; return Ok(()); }
                            }
                        }
                        _ => { unreachable!() }
                    };

                let ints_list =
                        {   let digest_alg  =
                               match algorithm {
                                  "sha256" =>     { hkdf::HKDF_SHA256 }
                                  "sha384" =>     { hkdf::HKDF_SHA384 }
                                  "sha512" =>     { hkdf::HKDF_SHA512 }
                                  _ =>            { self.fail = true; return Ok(()); }
                               };
                             let salt = hkdf::Salt::new(digest_alg, &salt);
                             let mut bytes : Vec<u8> = Vec::new();
                             bytes.resize(length, 0);
                             match salt.extract(&data).expand(&[&info[..]], MyKey(length)) {
                                 Ok(r) => { r.fill(&mut bytes).unwrap(); }
                                 _ => { self.fail = true; return Ok(()); }
                             }

                             Addr::HeapCell(self.heap.to_list(bytes.iter().map(|b| HeapCellValue::from(Addr::Fixnum(*b as isize)))))
                        };

                self.unify(self[temp_v!(6)], ints_list);
            }
            &SystemClauseType::CryptoPasswordHash => {
                let stub1 = MachineError::functor_stub(clause_name!("crypto_password_hash"), 3);
                let data = self.integers_to_bytevec(temp_v!(1), stub1);
                let stub2 = MachineError::functor_stub(clause_name!("crypto_password_hash"), 3);
                let salt = self.integers_to_bytevec(temp_v!(2), stub2);

                let iterations =
                    match Number::try_from((self[temp_v!(3)], &self.heap)) {
                        Ok(Number::Fixnum(n)) => {
                            u64::try_from(n).unwrap()
                        }
                        Ok(Number::Integer(n)) => {
                            match n.to_u64() {
                                Some(i) => { i }
                                None => { self.fail = true; return Ok(()); }
                            }
                        }
                        _ => {
                            unreachable!()
                        }
                    };

                let ints_list =
                        {   let mut bytes = [0u8; digest::SHA512_OUTPUT_LEN];
                            pbkdf2::derive(pbkdf2::PBKDF2_HMAC_SHA512,
                                           NonZeroU32::new(iterations as u32).unwrap(), &salt,
                                           &data, &mut bytes);

                             Addr::HeapCell(self.heap.to_list(bytes.iter().map(|b| HeapCellValue::from(Addr::Fixnum(*b as isize)))))
                        };

                self.unify(self[temp_v!(4)], ints_list);
            }
            &SystemClauseType::CryptoDataEncrypt => {
                let stub1 = MachineError::functor_stub(clause_name!("crypto_data_encrypt"), 6);
                let data = self.integers_to_bytevec(temp_v!(1), stub1);
                let stub2 = MachineError::functor_stub(clause_name!("crypto_data_encrypt"), 6);
                let key = self.integers_to_bytevec(temp_v!(2), stub2);
                let stub3 = MachineError::functor_stub(clause_name!("crypto_data_encrypt"), 6);
                let iv = self.integers_to_bytevec(temp_v!(3), stub3);

                let unbound_key = aead::UnboundKey::new(&aead::CHACHA20_POLY1305, &key).unwrap();
                let nonce = aead::Nonce::try_assume_unique_for_key(&iv).unwrap();
                let key = aead::LessSafeKey::new(unbound_key);

                let mut in_out = data.clone();
                let tag =
                     match key.seal_in_place_separate_tag(nonce, aead::Aad::empty(), &mut in_out) {
                        Ok(d) => { d }
                        _     => { self.fail = true; return Ok(()); }
                      };

                let tag_list =
                      Addr::HeapCell(self.heap.to_list(tag.as_ref().iter().map(|b| HeapCellValue::from(Addr::Fixnum(*b as isize)))));

                let complete_string = {
                          let buffer = String::from_iter(in_out.iter().map(|b| *b as char));
                          self.heap.put_complete_string(&buffer)
                      };

                self.unify(self[temp_v!(4)], tag_list);
                self.unify(self[temp_v!(5)], complete_string);
            }
            &SystemClauseType::CryptoDataDecrypt => {
                let stub1 = MachineError::functor_stub(clause_name!("crypto_data_decrypt"), 6);
                let data = self.integers_to_bytevec(temp_v!(1), stub1);
                let stub2 = MachineError::functor_stub(clause_name!("crypto_data_decrypt"), 6);
                let key = self.integers_to_bytevec(temp_v!(2), stub2);
                let stub3 = MachineError::functor_stub(clause_name!("crypto_data_decrypt"), 6);
                let iv = self.integers_to_bytevec(temp_v!(3), stub3);

                let encoding = match self.store(self.deref(self[temp_v!(4)])) {
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(ref atom, _) = &self.heap[h] {
                            atom.as_str()
                        } else {
                            unreachable!()
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                };

                let unbound_key = aead::UnboundKey::new(&aead::CHACHA20_POLY1305, &key).unwrap();
                let nonce = aead::Nonce::try_assume_unique_for_key(&iv).unwrap();
                let key = aead::LessSafeKey::new(unbound_key);

                let mut in_out = data.clone();

                let complete_string = {
                          let decrypted_data =
                                match key.open_in_place(nonce, aead::Aad::empty(), &mut in_out) {
                                   Ok(d) => { d }
                                   _     => { self.fail = true; return Ok(()); }
                                 };

                          let buffer = match encoding {
                                  "octet" => { String::from_iter(decrypted_data.iter().map(|b| *b as char)) }
                                  "utf8"  => { match String::from_utf8(decrypted_data.to_vec()) {
                                                  Ok(str) => { str }
                                                  _ => { self.fail = true; return Ok(()); }
                                                  }
                                               }
                                  _ => { unreachable!() }
                               };

                          self.heap.put_complete_string(&buffer)
                      };

                self.unify(self[temp_v!(5)], complete_string);
            }
            &SystemClauseType::CryptoEd25519Sign => {
                let stub1 = MachineError::functor_stub(clause_name!("crypto_ed25519_sign"), 4);
                let key = self.integers_to_bytevec(temp_v!(1), stub1);
                let stub2 = MachineError::functor_stub(clause_name!("crypto_ed25519_sign"), 4);
                let data = self.integers_to_bytevec(temp_v!(2), stub2);

                let key_pair = match signature::Ed25519KeyPair::from_pkcs8_maybe_unchecked(&key) {
                                  Ok(kp) => { kp }
                                  _ => { self.fail = true; return Ok(()); }
                               };

                let sig = key_pair.sign(&data);

                let sig_list =
                      Addr::HeapCell(self.heap.to_list(sig.as_ref().iter().map(|b| HeapCellValue::from(Addr::Fixnum(*b as isize)))));

                self.unify(self[temp_v!(3)], sig_list);
            }
            &SystemClauseType::CryptoEd25519Verify => {
                let stub1 = MachineError::functor_stub(clause_name!("crypto_ed25519_verify"), 4);
                let key = self.integers_to_bytevec(temp_v!(1), stub1);
                let stub2 = MachineError::functor_stub(clause_name!("crypto_ed25519_verify"), 4);
                let data = self.integers_to_bytevec(temp_v!(2), stub2);
                let stub3 = MachineError::functor_stub(clause_name!("crypto_ed25519_verify"), 4);
                let signature = self.integers_to_bytevec(temp_v!(3), stub3);

                let peer_public_key =
                    signature::UnparsedPublicKey::new(&signature::ED25519, &key);
                match peer_public_key.verify(&data, &signature) {
                    Ok(_) => { }
                    _ => { self.fail = true; return Ok(()); }
                }
            }
        };

        return_from_clause!(self.last_call, self)
    }
}


fn rng() -> &'static dyn SecureRandom {
    use std::ops::Deref;

    lazy_static! {
        static ref RANDOM: SystemRandom = SystemRandom::new();
    }

    RANDOM.deref()
}

struct MyKey<T: core::fmt::Debug + PartialEq>(T);

impl hkdf::KeyType for MyKey<usize> {
    fn len(&self) -> usize {
        self.0
    }
}
