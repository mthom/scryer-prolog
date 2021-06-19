use prolog_parser::ast::*;
use prolog_parser::parser::*;
use prolog_parser::{
    alpha_char, alpha_numeric_char, binary_digit_char, clause_name, decimal_digit_char,
    exponent_char, graphic_char, graphic_token_char, hexadecimal_digit_char, layout_char,
    meta_char, new_line_char, octal_digit_char, octet_char, prolog_char, sign_char, solo_char,
    symbolic_control_char, symbolic_hexadecimal_char, temp_v,
};

use lazy_static::lazy_static;

use crate::clause_types::*;
use crate::forms::*;
use crate::heap_print::*;
use crate::instructions::*;
use crate::machine;
use crate::machine::code_repo::CodeRepo;
use crate::machine::code_walker::*;
use crate::machine::copier::*;
use crate::machine::machine_errors::*;
use crate::machine::machine_indices::*;
use crate::machine::machine_state::*;
use crate::machine::preprocessor::to_op_decl;
use crate::machine::streams::*;

use crate::read::readline;
use crate::rug::Integer;
use ordered_float::OrderedFloat;

use indexmap::IndexSet;

use ref_thread_local::RefThreadLocal;

use std::collections::BTreeSet;
use std::convert::TryFrom;
use std::env;
use std::fs;
use std::io::{ErrorKind, Read, Write};
use std::iter::{once, FromIterator};
use std::net::{TcpListener, TcpStream};
use std::num::NonZeroU32;
use std::ops::Sub;
use std::rc::Rc;
use std::process;

use chrono::{offset::Local, DateTime};
use cpu_time::ProcessTime;
use std::time::{Duration, SystemTime};

use crossterm::event::{read, Event, KeyCode, KeyEvent, KeyModifiers};
use crossterm::terminal::{disable_raw_mode, enable_raw_mode};

use blake2::{Blake2b, Blake2s};
use ring::rand::{SecureRandom, SystemRandom};
use ring::{
    aead, digest, hkdf, pbkdf2,
    signature::{self, KeyPair},
};
use ripemd160::{Digest, Ripemd160};
use sha3::{Sha3_224, Sha3_256, Sha3_384, Sha3_512};

use openssl::bn::{BigNum, BigNumContext};
use openssl::ec::{EcGroup, EcPoint};
use openssl::nid::Nid;

use sodiumoxide::crypto::scalarmult::curve25519::*;

use native_tls::TlsConnector;

use base64;
use roxmltree;
use select;

pub(crate) fn get_key() -> KeyEvent {
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
                    }
                    _ => (),
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
            Addr::PStrLocation(h, n) => CycleSearchResult::PStrLocation(self.steps, h, n),
            Addr::EmptyList => CycleSearchResult::ProperList(self.steps),
            _ => CycleSearchResult::NotList,
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
            Addr::EmptyList => Some(CycleSearchResult::ProperList(brent_st.steps)),
            addr @ Addr::HeapCell(_) | addr @ Addr::StackCell(..) | addr @ Addr::AttrVar(_) => {
                Some(CycleSearchResult::PartialList(
                    brent_st.steps,
                    addr.as_var().unwrap(),
                ))
            }
            Addr::PStrLocation(h, n) => match &self.heap[h] {
                HeapCellValue::PartialString(ref pstr, _) => {
                    if let Some(c) = pstr.range_from(n..).next() {
                        brent_st.step(Addr::PStrLocation(h, n + c.len_utf8()))
                    } else {
                        unreachable!()
                    }
                }
                _ => {
                    unreachable!()
                }
            },
            Addr::Lis(l) => brent_st.step(Addr::HeapCell(l + 1)),
            _ => Some(CycleSearchResult::NotList),
        }
    }

    pub(super) fn detect_cycles_with_max(&self, max_steps: usize, addr: Addr) -> CycleSearchResult {
        let hare = match self.store(self.deref(addr)) {
            Addr::Lis(offset) if max_steps > 0 => Addr::Lis(offset),
            Addr::Lis(offset) => {
                return CycleSearchResult::UntouchedList(offset);
            }
            Addr::PStrLocation(h, n) if max_steps > 0 => Addr::PStrLocation(h, n),
            Addr::PStrLocation(h, _) => {
                return CycleSearchResult::UntouchedList(h);
            }
            Addr::EmptyList => {
                return CycleSearchResult::EmptyList;
            }
            Addr::Con(h) if max_steps > 0 => {
                if let HeapCellValue::PartialString(..) = &self.heap[h] {
                    Addr::PStrLocation(h, 0)
                } else {
                    return CycleSearchResult::NotList;
                }
            }
            Addr::Con(h) => {
                if let HeapCellValue::PartialString(..) = &self.heap[h] {
                    return CycleSearchResult::UntouchedList(h);
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

    pub(super) fn detect_cycles(&self, addr: Addr) -> CycleSearchResult {
        let addr = self.store(self.deref(addr));
        let hare = match addr {
            Addr::Lis(offset) => Addr::Lis(offset),
            Addr::EmptyList => {
                return CycleSearchResult::EmptyList;
            }
            Addr::PStrLocation(h, n) => Addr::PStrLocation(h, n),
            Addr::Con(h) => {
                if let HeapCellValue::PartialString(..) = &self.heap[h] {
                    Addr::PStrLocation(h, 0)
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
        let search_result = if let Some(max_steps) = max_steps {
            if max_steps == -1 {
                self.detect_cycles(self[temp_v!(3)])
            } else {
                self.detect_cycles_with_max(max_steps as usize, self[temp_v!(3)])
            }
        } else {
            self.detect_cycles(self[temp_v!(3)])
        };

        match search_result {
            CycleSearchResult::PStrLocation(steps, h, n) => {
                self.finalize_skip_max_list(steps, Addr::PStrLocation(h, n));
            }
            CycleSearchResult::UntouchedList(l) => self.finalize_skip_max_list(0, Addr::Lis(l)),
            CycleSearchResult::EmptyList => self.finalize_skip_max_list(0, Addr::EmptyList),
            CycleSearchResult::PartialList(n, r) => self.finalize_skip_max_list(n, r.as_addr()),
            CycleSearchResult::ProperList(steps) => {
                self.finalize_skip_max_list(steps, Addr::EmptyList)
            }
            CycleSearchResult::NotList => {
                let xs0 = self[temp_v!(3)];
                self.finalize_skip_max_list(0, xs0);
            }
        };
    }

    pub(super) fn skip_max_list(&mut self) -> CallResult {
        let max_steps = self.store(self.deref(self[temp_v!(2)]));

        match max_steps {
            Addr::HeapCell(_) | Addr::StackCell(..) | Addr::AttrVar(_) => {
                let stub = MachineError::functor_stub(clause_name!("$skip_max_list"), 4);
                return Err(self.error_form(MachineError::instantiation_error(), stub));
            }
            addr => {
                let max_steps_n = match Number::try_from((max_steps, &self.heap)) {
                    Ok(Number::Integer(n)) => n.to_isize(),
                    Ok(Number::Fixnum(n)) => Some(n),
                    _ => None,
                };

                if max_steps_n.map(|i| i >= -1).unwrap_or(false) {
                    let n = self.store(self.deref(self[temp_v!(1)]));

                    match Number::try_from((n, &self.heap)) {
                        Ok(Number::Integer(n)) => {
                            if n.as_ref() == &0 {
                                let xs0 = self[temp_v!(3)];
                                let xs = self[temp_v!(4)];

                                self.unify(xs0, xs);
                            } else {
                                self.skip_max_list_result(max_steps_n);
                            }
                        }
                        Ok(Number::Fixnum(n)) => {
                            if n == 0 {
                                let xs0 = self[temp_v!(3)];
                                let xs = self[temp_v!(4)];

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
                    return Err(self.error_form(
                        MachineError::type_error(self.heap.h(), ValidType::Integer, addr),
                        stub,
                    ));
                }
            }
        }

        Ok(())
    }

    fn stream_from_file_spec(
        &self,
        file_spec: ClauseName,
        indices: &mut IndexStore,
        options: &StreamOptions,
    ) -> Result<Stream, MachineStub> {
        if file_spec.as_str().is_empty() {
            let stub = MachineError::functor_stub(clause_name!("open"), 4);
            let err = MachineError::domain_error(DomainErrorType::SourceSink, self[temp_v!(1)]);

            return Err(self.error_form(err, stub));
        }

        // 8.11.5.3l)
        if let Some(ref alias) = &options.alias {
            if indices.stream_aliases.contains_key(alias) {
                return Err(self.occupied_alias_permission_error(alias.clone(), "open", 4));
            }
        }

        let mode = atom_from!(self, self.store(self.deref(self[temp_v!(2)])));
        let mut open_options = fs::OpenOptions::new();

        let (is_input_file, in_append_mode) = match mode.as_str() {
            "read" => {
                open_options.read(true).write(false).create(false);
                (true, false)
            }
            "write" => {
                open_options
                    .read(false)
                    .write(true)
                    .truncate(true)
                    .create(true);
                (false, false)
            }
            "append" => {
                open_options
                    .read(false)
                    .write(true)
                    .create(true)
                    .append(true);
                (false, true)
            }
            _ => {
                let stub = MachineError::functor_stub(clause_name!("open"), 4);
                let err = MachineError::domain_error(DomainErrorType::IOMode, self[temp_v!(2)]);

                // 8.11.5.3h)
                return Err(self.error_form(err, stub));
            }
        };

        let file = match open_options.open(file_spec.as_str()) {
            Ok(file) => file,
            Err(err) => {
                match err.kind() {
                    ErrorKind::NotFound => {
                        // 8.11.5.3j)
                        let stub = MachineError::functor_stub(clause_name!("open"), 4);

                        let err = MachineError::existence_error(
                            self.heap.h(),
                            ExistenceError::SourceSink(self[temp_v!(1)]),
                        );

                        return Err(self.error_form(err, stub));
                    }
                    ErrorKind::PermissionDenied => {
                        // 8.11.5.3k)
                        return Err(self.open_permission_error(self[temp_v!(1)], "open", 4));
                    }
                    _ => {
                        let stub = MachineError::functor_stub(clause_name!("open"), 4);

                        let err = MachineError::syntax_error(self.heap.h(), ParserError::IO(err));

                        return Err(self.error_form(err, stub));
                    }
                }
            }
        };

        Ok(if is_input_file {
            Stream::from_file_as_input(file_spec, file)
        } else {
            Stream::from_file_as_output(file_spec, file, in_append_mode)
        })
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

        let mut copy_ball_term =
            CopyBallTerm::new(&mut self.stack, &mut self.heap, &mut self.lifted_heap);

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
                    self.lifted_heap
                        .push(HeapCellValue::Addr(addr_constr(threshold)));
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
                            &CompositeOpDir::new(&indices.op_dir, None),
                        );

                        let addr = self
                            .heap
                            .to_unifiable(HeapCellValue::DBRef(DBRef::NamedPred(
                                name.clone(),
                                *arity,
                                spec,
                            )));

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
                            let addr = self.heap.to_unifiable(HeapCellValue::DBRef(DBRef::Op(
                                *priority,
                                *spec,
                                name.clone(),
                                op_dir.clone(),
                                SharedOpDesc::new(*priority, *spec),
                            )));

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
    ) -> Result<char, MachineStub> {
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

        let mut stream = match parsing_stream(std::io::Cursor::new(string)) {
            Ok(stream) => stream,
            Err(e) => {
                let err = MachineError::session_error(self.heap.h(), SessionError::from(e));

                return Err(self.error_form(err, stub));
            }
        };

        let mut parser = Parser::new(&mut stream, self.atom_tbl.clone(), self.machine_flags());

        match parser.read_term(&CompositeOpDir::new(&indices.op_dir, None)) {
            Err(err) => {
                let h = self.heap.h();
                let err = MachineError::syntax_error(h, err);

                return Err(self.error_form(err, stub));
            }
            Ok(Term::Constant(_, Constant::Rational(n))) => {
                let addr = self.heap.put_constant(Constant::Rational(n));
                (self.unify_fn)(self, nx, addr);
            }
            Ok(Term::Constant(_, Constant::Float(n))) => {
                let addr = self.heap.put_constant(Constant::Float(n));
                (self.unify_fn)(self, nx, addr);
            }
            Ok(Term::Constant(_, Constant::Integer(n))) => {
                let addr = self.heap.put_constant(Constant::Integer(n));
                (self.unify_fn)(self, nx, addr);
            }
            Ok(Term::Constant(_, Constant::Fixnum(n))) => {
                let addr = self.heap.put_constant(Constant::Fixnum(n));
                (self.unify_fn)(self, nx, addr);
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

    fn call_continuation_chunk(&mut self, chunk: Addr, return_p: LocalCodePtr) -> LocalCodePtr {
        let chunk = self.store(self.deref(chunk));

        match chunk {
            Addr::Str(s) => {
                match &self.heap[s] {
                    HeapCellValue::NamedStr(arity, ..) => {
                        let num_cells = arity - 1;
                        let p_functor = self.heap[s + 1].as_addr(s + 1);

                        let cp = self.heap.to_local_code_ptr(&p_functor).unwrap();
                        let prev_e = self.e;

                        let e = self.stack.allocate_and_frame(num_cells);
                        let and_frame = self.stack.index_and_frame_mut(e);

                        and_frame.prelude.e = prev_e;
                        and_frame.prelude.cp = return_p;

                        self.p = CodePtr::Local(cp + 1);

                        // adjust cut point to occur after call_continuation.
                        if num_cells > 0 {
                            if let Addr::CutPoint(_) = self.heap[s + 2].as_addr(s + 2) {
                                and_frame[1] = Addr::CutPoint(self.b);
                            } else {
                                and_frame[1] = self.heap[s + 2].as_addr(s + 2);
                            }
                        }

                        for index in s + 3..s + 2 + num_cells {
                            and_frame[index - (s + 1)] = self.heap[index].as_addr(index);
                        }

                        self.e = e;

                        self.p.local()
                    }
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        }
    }

    pub(super) fn system_call(
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
            &SystemClauseType::BindFromRegister => {
                let reg = self.store(self.deref(self[temp_v!(2)]));
                let n = match Number::try_from((reg, &self.heap)) {
                    Ok(Number::Integer(n)) => n.to_usize(),
                    Ok(Number::Fixnum(n)) => usize::try_from(n).ok(),
                    _ => {
                        unreachable!()
                    }
                };

                if let Some(n) = n {
                    if n <= MAX_ARITY {
                        let target = self[temp_v!(n)];
                        let addr = self[temp_v!(1)];

                        (self.unify_fn)(self, addr, target);
                        return return_from_clause!(self.last_call, self);
                    }
                }

                self.fail = true;
            }
            &SystemClauseType::CurrentHostname => {
                match hostname::get().ok() {
                    Some(host) => match host.into_string().ok() {
                        Some(host) => {
                            let hostname = self.heap.to_unifiable(HeapCellValue::Atom(
                                clause_name!(host, self.atom_tbl),
                                None,
                            ));

                            (self.unify_fn)(self, self[temp_v!(1)], hostname);
                            return return_from_clause!(self.last_call, self);
                        }
                        None => {}
                    },
                    None => {}
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
                        (self.unify_fn)(self, stream, addr);
                    }
                    Addr::Stream(other_stream) => {
                        if let HeapCellValue::Stream(ref other_stream) = &self.heap[other_stream] {
                            self.fail = current_input_stream != other_stream;
                        } else {
                            unreachable!()
                        }
                    }
                    addr => {
                        let stub = MachineError::functor_stub(clause_name!("current_input"), 1);

                        let err = MachineError::domain_error(DomainErrorType::Stream, addr);

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
                        (self.unify_fn)(self, stream, addr);
                    }
                    Addr::Stream(other_stream) => {
                        if let HeapCellValue::Stream(ref other_stream) = &self.heap[other_stream] {
                            self.fail = current_output_stream != other_stream;
                        } else {
                            unreachable!()
                        }
                    }
                    addr => {
                        let stub = MachineError::functor_stub(clause_name!("current_input"), 1);

                        let err = MachineError::domain_error(DomainErrorType::Stream, addr);

                        return Err(self.error_form(err, stub));
                    }
                }
            }
            &SystemClauseType::DirectoryFiles => {
                let dir = self.heap_pstr_iter(self[temp_v!(1)]).to_string();
                let path = std::path::Path::new(&dir);
                let mut files = Vec::new();

                if let Ok(entries) = fs::read_dir(path) {
                    for entry in entries {
                        if let Ok(entry) = entry {
                            match entry.file_name().into_string() {
                                Ok(name) => {
                                    files.push(self.heap.put_complete_string(&name));
                                }
                                _ => {
                                    let stub = MachineError::functor_stub(
                                        clause_name!("directory_files"),
                                        2,
                                    );
                                    let err =
                                        MachineError::representation_error(RepFlag::Character);
                                    let err = self.error_form(err, stub);

                                    return Err(err);
                                }
                            }
                        }
                    }
                }

                let files_list = Addr::HeapCell(self.heap.to_list(files.into_iter()));
                (self.unify_fn)(self, self[temp_v!(2)], files_list);
            }
            &SystemClauseType::FileSize => {
                let file = self.heap_pstr_iter(self[temp_v!(1)]).to_string();
                let len = Integer::from(fs::metadata(&file).unwrap().len());

                let len = self.heap.to_unifiable(HeapCellValue::Integer(Rc::new(len)));

                (self.unify_fn)(self, self[temp_v!(2)], len);
            }
            &SystemClauseType::FileExists => {
                let file = self.heap_pstr_iter(self[temp_v!(1)]).to_string();
                if !std::path::Path::new(&file).exists() || !fs::metadata(&file).unwrap().is_file()
                {
                    self.fail = true;
                    return Ok(());
                }
            }
            &SystemClauseType::DirectoryExists => {
                let directory = self.heap_pstr_iter(self[temp_v!(1)]).to_string();
                if !std::path::Path::new(&directory).exists()
                    || !fs::metadata(&directory).unwrap().is_dir()
                {
                    self.fail = true;
                    return Ok(());
                }
            }
            &SystemClauseType::DirectorySeparator => {
                let addr = self
                    .heap
                    .put_constant(Constant::Char(std::path::MAIN_SEPARATOR));
                (self.unify_fn)(self, self[temp_v!(1)], addr);
            }
            &SystemClauseType::MakeDirectory => {
                let directory = self.heap_pstr_iter(self[temp_v!(1)]).to_string();

                match fs::create_dir(directory) {
                    Ok(_) => {}
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                }
            }
            &SystemClauseType::MakeDirectoryPath => {
                let directory = self.heap_pstr_iter(self[temp_v!(1)]).to_string();

                match fs::create_dir_all(directory) {
                    Ok(_) => {}
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                }
            }
            &SystemClauseType::DeleteFile => {
                let file = self.heap_pstr_iter(self[temp_v!(1)]).to_string();

                match fs::remove_file(file) {
                    Ok(_) => {}
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                }
            }
            &SystemClauseType::RenameFile => {
                let file = self.heap_pstr_iter(self[temp_v!(1)]).to_string();
                let renamed = self.heap_pstr_iter(self[temp_v!(2)]).to_string();

                match fs::rename(file, renamed) {
                    Ok(_) => {}
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                }
            }
            &SystemClauseType::DeleteDirectory => {
                let directory = self.heap_pstr_iter(self[temp_v!(1)]).to_string();

                match fs::remove_dir(directory) {
                    Ok(_) => {}
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                }
            }
            &SystemClauseType::WorkingDirectory => {
                if let Ok(dir) = env::current_dir() {
                    let current = match dir.to_str() {
                        Some(d) => d,
                        _ => {
                            let stub =
                                MachineError::functor_stub(clause_name!("working_directory"), 2);
                            let err = MachineError::representation_error(RepFlag::Character);
                            let err = self.error_form(err, stub);

                            return Err(err);
                        }
                    };

                    let chars = self.heap.put_complete_string(current);
                    (self.unify_fn)(self, self[temp_v!(1)], chars);

                    let next = self.heap_pstr_iter(self[temp_v!(2)]).to_string();

                    match env::set_current_dir(std::path::Path::new(&next)) {
                        Ok(_) => {}
                        _ => {
                            self.fail = true;
                            return Ok(());
                        }
                    }
                } else {
                    self.fail = true;
                    return Ok(());
                }
            }
            &SystemClauseType::PathCanonical => {
                let path = self.heap_pstr_iter(self[temp_v!(1)]).to_string();

                match fs::canonicalize(path) {
                    Ok(canonical) => {
                        let cs = match canonical.to_str() {
                            Some(s) => s,
                            _ => {
                                let stub =
                                    MachineError::functor_stub(clause_name!("path_canonical"), 2);
                                let err = MachineError::representation_error(RepFlag::Character);
                                let err = self.error_form(err, stub);

                                return Err(err);
                            }
                        };
                        let chars = self.heap.put_complete_string(cs);
                        (self.unify_fn)(self, self[temp_v!(2)], chars);
                    }
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                }
            }
            &SystemClauseType::FileTime => {
                let file = self.heap_pstr_iter(self[temp_v!(1)]).to_string();

                let which = match self.store(self.deref(self[temp_v!(2)])) {
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

                if let Ok(md) = fs::metadata(file) {
                    if let Ok(time) = match which {
                        "modification" => md.modified(),
                        "access" => md.accessed(),
                        "creation" => md.created(),
                        _ => {
                            unreachable!()
                        }
                    } {
                        let chars = self.systemtime_to_timestamp(time);
                        (self.unify_fn)(self, self[temp_v!(3)], chars);
                    } else {
                        self.fail = true;
                        return Ok(());
                    }
                } else {
                    self.fail = true;
                    return Ok(());
                }
            }
            &SystemClauseType::AtomChars => {
                let a1 = self[temp_v!(1)];

                match self.store(self.deref(a1)) {
                    Addr::Char(c) => {
                        let iter = once(Addr::Char(c));
                        let list_of_chars = Addr::HeapCell(self.heap.to_list(iter));

                        let a2 = self[temp_v!(2)];
                        (self.unify_fn)(self, a2, list_of_chars);
                    }
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(name, _) = self.heap.clone(h) {
                            let s = self.heap.put_complete_string(name.as_str());
                            let a2 = self[temp_v!(2)];

                            (self.unify_fn)(self, s, a2);
                        } else {
                            unreachable!()
                        }
                    }
                    Addr::EmptyList => {
                        let a2 = self[temp_v!(2)];
                        let chars = vec![Addr::Char('['), Addr::Char(']')];

                        let list_of_chars = Addr::HeapCell(self.heap.to_list(chars.into_iter()));

                        (self.unify_fn)(self, a2, list_of_chars);
                    }
                    addr if addr.is_ref() => {
                        let mut iter = self.heap_pstr_iter(self[temp_v!(2)]);
                        let string = iter.to_string();

                        match iter.focus() {
                            Addr::EmptyList => {
                                if &string == "[]" {
                                    (self.unify_fn)(self, addr, Addr::EmptyList);
                                } else {
                                    let chars = clause_name!(string, self.atom_tbl);
                                    let atom =
                                        self.heap.to_unifiable(HeapCellValue::Atom(chars, None));

                                    (self.unify_fn)(self, addr, atom);
                                }
                            }
                            focus => {
                                if let Addr::Lis(l) = focus {
                                    let stub =
                                        MachineError::functor_stub(clause_name!("atom_chars"), 2);

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
                        (self.unify_fn)(self, a2, list_of_codes);
                    }
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(name, _) = self.heap.clone(h) {
                            let a2 = self.store(self.deref(self[temp_v!(2)]));

                            let iter = name.as_str().chars().map(|c| Addr::Fixnum(c as isize));

                            let list_of_codes = Addr::HeapCell(self.heap.to_list(iter));

                            (self.unify_fn)(self, a2, list_of_codes);
                        } else {
                            unreachable!()
                        }
                    }
                    Addr::EmptyList => {
                        let chars = vec![Addr::Fixnum('[' as isize), Addr::Fixnum(']' as isize)];

                        let list_of_codes = Addr::HeapCell(self.heap.to_list(chars.into_iter()));
                        let a2 = self[temp_v!(2)];

                        (self.unify_fn)(self, a2, list_of_codes);
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

                                let string = self.heap.to_unifiable(HeapCellValue::Atom(
                                    clause_name!(chars, self.atom_tbl),
                                    None,
                                ));

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
                        clause_name!(c.to_string(), self.atom_tbl)
                    }
                    _ => {
                        unreachable!()
                    }
                };

                let len = Integer::from(atom.as_str().chars().count());
                let len = self.heap.to_unifiable(HeapCellValue::Integer(Rc::new(len)));

                let a2 = self[temp_v!(2)];

                (self.unify_fn)(self, a2, len);
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
                    Ok(addrs) => match self.try_char_list(addrs) {
                        Ok(string) => {
                            let stub = MachineError::functor_stub(clause_name!("number_chars"), 2);
                            self.parse_number_from_string(string, indices, stub)?;
                        }
                        Err(err) => {
                            let stub = MachineError::functor_stub(clause_name!("number_chars"), 2);

                            return Err(self.error_form(err, stub));
                        }
                    },
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

                if atom.as_str().is_empty() {
                    self.fail = true;
                    return Ok(());
                }

                let pstr = self.heap.allocate_pstr(atom.as_str());
                (self.unify_fn)(self, self[temp_v!(2)], pstr);

                if !self.fail {
                    let h = self.heap.h();
                    let pstr_tail = self.heap[h - 1].as_addr(h - 1);

                    (self.unify_fn)(self, self[temp_v!(3)], pstr_tail);
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
                    _ => {}
                }

                let mut heap_pstr_iter = self.heap_pstr_iter(addr);

                while let Some(_) = heap_pstr_iter.next() {}

                self.fail = match heap_pstr_iter.focus() {
                    Addr::AttrVar(_)
                    | Addr::HeapCell(_)
                    | Addr::StackCell(..)
                    | Addr::EmptyList => false,
                    _ => true,
                };
            }
            &SystemClauseType::PartialStringTail => {
                let pstr = self.store(self.deref(self[temp_v!(1)]));

                match pstr {
                    Addr::PStrLocation(h, _) => {
                        if let HeapCellValue::PartialString(_, true) = &self.heap[h] {
                            let tail = self.heap[h + 1].as_addr(h + 1);
                            let target = self[temp_v!(2)];

                            (self.unify_fn)(self, tail, target);
                        } else {
                            self.fail = true;
                            return Ok(());
                        }
                    }
                    Addr::Lis(h) => {
                        (self.unify_fn)(self, Addr::HeapCell(h + 1), self[temp_v!(2)]);
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
                let mut stream = self.get_stream_or_alias(
                    self[temp_v!(1)],
                    &indices.stream_aliases,
                    "peek_byte",
                    2,
                )?;

                self.check_stream_properties(
                    &mut stream,
                    StreamType::Binary,
                    Some(self[temp_v!(2)]),
                    clause_name!("peek_byte"),
                    2,
                )?;

                if stream.past_end_of_stream() {
                    if EOFAction::Reset != stream.options().eof_action {
                        return return_from_clause!(self.last_call, self);
                    } else if self.fail {
                        return Ok(());
                    }
                }

                if stream.at_end_of_stream() {
                    stream.set_past_end_of_stream();
                    (self.unify_fn)(self, self[temp_v!(2)], Addr::Fixnum(-1));
                    return return_from_clause!(self.last_call, self);
                }

                let addr = match self.store(self.deref(self[temp_v!(2)])) {
                    addr if addr.is_ref() => addr,
                    addr => match Number::try_from((addr, &self.heap)) {
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
                    },
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

                            if EOFAction::Reset != stream.options().eof_action {
                                return return_from_clause!(self.last_call, self);
                            } else if self.fail {
                                return Ok(());
                            }
                        }
                    }
                }
            }
            &SystemClauseType::PeekChar => {
                let mut stream = self.get_stream_or_alias(
                    self[temp_v!(1)],
                    &indices.stream_aliases,
                    "peek_char",
                    2,
                )?;

                self.check_stream_properties(
                    &mut stream,
                    StreamType::Text,
                    Some(self[temp_v!(2)]),
                    clause_name!("peek_char"),
                    2,
                )?;

                if stream.past_end_of_stream() {
                    if EOFAction::Reset != stream.options().eof_action {
                        return return_from_clause!(self.last_call, self);
                    } else if self.fail {
                        return Ok(());
                    }
                }

                if stream.at_end_of_stream() {
                    let end_of_file = clause_name!("end_of_file");
                    let end_of_file = self
                        .heap
                        .to_unifiable(HeapCellValue::Atom(end_of_file, None));

                    stream.set_past_end_of_stream();

                    (self.unify_fn)(self, self[temp_v!(2)], end_of_file);
                    return return_from_clause!(self.last_call, self);
                }

                let addr = match self.store(self.deref(self[temp_v!(2)])) {
                    addr if addr.is_ref() => addr,
                    Addr::Con(h) if self.heap.atom_at(h) => match &self.heap[h] {
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
                    },
                    Addr::Char(d) => Addr::Char(d),
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

                            if EOFAction::Reset != stream.options().eof_action {
                                return return_from_clause!(self.last_call, self);
                            } else if self.fail {
                                return Ok(());
                            }
                        } /*
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
                let mut stream = self.get_stream_or_alias(
                    self[temp_v!(1)],
                    &indices.stream_aliases,
                    "peek_code",
                    2,
                )?;

                self.check_stream_properties(
                    &mut stream,
                    StreamType::Text,
                    Some(self[temp_v!(2)]),
                    clause_name!("peek_code"),
                    2,
                )?;

                if stream.past_end_of_stream() {
                    if EOFAction::Reset != stream.options().eof_action {
                        return return_from_clause!(self.last_call, self);
                    } else if self.fail {
                        return Ok(());
                    }
                }

                if stream.at_end_of_stream() {
                    let end_of_file = clause_name!("end_of_file");
                    let end_of_file = self
                        .heap
                        .to_unifiable(HeapCellValue::Atom(end_of_file, None));

                    stream.set_past_end_of_stream();

                    (self.unify_fn)(self, self[temp_v!(2)], end_of_file);
                    return return_from_clause!(self.last_call, self);
                }

                let addr = match self.store(self.deref(self[temp_v!(2)])) {
                    addr if addr.is_ref() => addr,
                    addr => match Number::try_from((addr, &self.heap)) {
                        Ok(Number::Integer(n)) => {
                            let n = n
                                .to_u32()
                                .and_then(|n| std::char::from_u32(n).and_then(|_| Some(n)));

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
                            let n = u32::try_from(n)
                                .ok()
                                .and_then(|n| std::char::from_u32(n).and_then(|_| Some(n)));

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
                    },
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

                            if EOFAction::Reset != stream.options().eof_action {
                                return return_from_clause!(self.last_call, self);
                            } else if self.fail {
                                return Ok(());
                            }
                        }
                    }
                }
            }
            &SystemClauseType::NumberToChars => {
                let n = self[temp_v!(1)];
                let chs = self[temp_v!(2)];

                let n = self.store(self.deref(n));

                let string = match Number::try_from((n, &self.heap)) {
                    Ok(Number::Float(OrderedFloat(n))) => {
                        format!("{0:<20?}", n)
                    }
                    Ok(Number::Fixnum(n)) => n.to_string(),
                    Ok(Number::Integer(n)) => n.to_string(),
                    Ok(Number::Rational(r)) => {
                        // n has already been confirmed as an integer, and
                        // internally, Rational is assumed reduced, so its denominator
                        // must be 1.
                        r.numer().to_string()
                    }
                    _ => {
                        unreachable!()
                    }
                };

                let chars = string.trim().chars().map(|c| Addr::Char(c));
                let char_list = Addr::HeapCell(self.heap.to_list(chars));

                (self.unify_fn)(self, char_list, chs);
            }
            &SystemClauseType::NumberToCodes => {
                let n = self[temp_v!(1)];
                let chs = self[temp_v!(2)];

                let string = match Number::try_from((n, &self.heap)) {
                    Ok(Number::Float(OrderedFloat(n))) => {
                        format!("{0:<20?}", n)
                    }
                    Ok(Number::Fixnum(n)) => n.to_string(),
                    Ok(Number::Integer(n)) => n.to_string(),
                    Ok(Number::Rational(r)) => {
                        // n has already been confirmed as an integer, and
                        // internally, Rational is assumed reduced, so its
                        // denominator must be 1.
                        r.numer().to_string()
                    }
                    _ => {
                        unreachable!()
                    }
                };

                let codes = string.trim().chars().map(|c| Addr::Fixnum(c as isize));

                let codes_list = Addr::HeapCell(self.heap.to_list(codes));

                (self.unify_fn)(self, codes_list, chs);
            }
            &SystemClauseType::CodesToNumber => {
                let stub = MachineError::functor_stub(clause_name!("number_codes"), 2);

                match self.try_from_list(temp_v!(1), stub) {
                    Err(e) => {
                        return Err(e);
                    }
                    Ok(addrs) => match self.try_char_list(addrs) {
                        Ok(chars) => {
                            let stub = MachineError::functor_stub(clause_name!("number_codes"), 2);
                            self.parse_number_from_string(chars, indices, stub)?;
                        }
                        Err(err) => {
                            let stub = MachineError::functor_stub(clause_name!("number_codes"), 2);

                            return Err(self.error_form(err, stub));
                        }
                    },
                }
            }
            &SystemClauseType::LiftedHeapLength => {
                let a1 = self[temp_v!(1)];
                let lh_len = Addr::Usize(self.lifted_heap.h());

                (self.unify_fn)(self, a1, lh_len);
            }
            &SystemClauseType::CharCode => {
                let a1 = self[temp_v!(1)];

                match self.store(self.deref(a1)) {
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        let c = if let HeapCellValue::Atom(name, _) = &self.heap[h] {
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
                        (self.unify_fn)(self, Addr::Fixnum(c as isize), a2);
                    }
                    Addr::Char(c) => {
                        let a2 = self[temp_v!(2)];
                        (self.unify_fn)(self, Addr::Fixnum(c as isize), a2);
                    }
                    addr if addr.is_ref() => {
                        let a2 = self[temp_v!(2)];
                        let a2 = self.store(self.deref(a2));

                        let c = match Number::try_from((a2, &self.heap)) {
                            Ok(Number::Integer(n)) => self.int_to_char(&n, "char_code", 2)?,
                            Ok(Number::Fixnum(n)) => {
                                self.int_to_char(&Integer::from(n), "char_code", 2)?
                            }
                            _ => {
                                self.fail = true;
                                return Ok(());
                            }
                        };

                        (self.unify_fn)(self, Addr::Char(c), addr);
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
                        } else {
                            unreachable!()
                        }
                    }
                    _ => unreachable!(),
                };
                let chars = match a2 {
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(name, _) = &self.heap[h] {
                            name.as_str().to_string()
                        } else {
                            unreachable!()
                        }
                    }
                    Addr::Char(c) => c.to_string(),
                    _ => unreachable!(),
                };
                self.fail = true; // This predicate fails by default.
                macro_rules! macro_check {
                    ($id:ident, $name:tt) => {
                        if $id!(c) && chars == $name {
                            self.fail = false;

                            return return_from_clause!(self.last_call, self);
                        }
                    };
                }
                macro_rules! method_check {
                    ($id:ident, $name:tt) => {
                        if c.$id() && chars == $name {
                            self.fail = false;

                            return return_from_clause!(self.last_call, self);
                        }
                    };
                }
                macro_check!(alpha_char, "alpha");
                method_check!(is_alphabetic, "alphabetic");
                method_check!(is_alphanumeric, "alphanumeric");
                macro_check!(alpha_numeric_char, "alnum");
                method_check!(is_ascii, "ascii");
                method_check!(is_ascii_punctuation, "ascii_ponctuaction");
                method_check!(is_ascii_graphic, "ascii_graphic");
                // macro_check!(backslash_char, "backslash");
                // macro_check!(back_quote_char, "back_quote");
                macro_check!(binary_digit_char, "binary_digit");
                // macro_check!(capital_letter_char, "upper");
                // macro_check!(comment_1_char, "comment_1");
                // macro_check!(comment_2_char, "comment_2");
                method_check!(is_control, "control");
                // macro_check!(cut_char, "cut");
                macro_check!(decimal_digit_char, "decimal_digit");
                // macro_check!(decimal_point_char, "decimal_point");
                // macro_check!(double_quote_char, "double_quote");
                macro_check!(exponent_char, "exponent");
                macro_check!(graphic_char, "graphic");
                macro_check!(graphic_token_char, "graphic_token");
                macro_check!(hexadecimal_digit_char, "hexadecimal_digit");
                macro_check!(layout_char, "layout");
                method_check!(is_lowercase, "lower");
                macro_check!(meta_char, "meta");
                // macro_check!(new_line_char, "new_line");
                method_check!(is_numeric, "numeric");
                macro_check!(octal_digit_char, "octal_digit");
                macro_check!(octet_char, "octet");
                macro_check!(prolog_char, "prolog");
                // macro_check!(semicolon_char, "semicolon");
                macro_check!(sign_char, "sign");
                // macro_check!(single_quote_char, "single_quote");
                // macro_check!(small_letter_char, "lower");
                macro_check!(solo_char, "solo");
                // macro_check!(space_char, "space");
                macro_check!(symbolic_hexadecimal_char, "symbolic_hexadecimal");
                macro_check!(symbolic_control_char, "symbolic_control");
                method_check!(is_uppercase, "upper");
                // macro_check!(variable_indicator_char, "variable_indicator");
                method_check!(is_whitespace, "whitespace");
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
                let (key_h, key) = match self.store(self.deref(self[temp_v!(1)])) {
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(ref atom, _) = &self.heap[h] {
                            (h, atom.clone())
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
                    Some((ref ball, ref mut loc)) => match loc {
                        Some(ref value_addr) => {
                            (self.unify_fn)(self, addr, *value_addr);
                        }
                        loc @ None if !ball.stub.is_empty() => {
                            let h = self.heap.h();
                            let stub = ball.copy_and_align(h);

                            self.heap.extend(stub.into_iter());
                            (self.unify_fn)(self, addr, Addr::HeapCell(h));

                            if !self.fail {
                                *loc = Some(Addr::HeapCell(h));
                                self.trail(TrailRef::BlackboardEntry(key_h));
                            }
                        }
                        _ => self.fail = true,
                    },
                    None => self.fail = true,
                };
            }
            &SystemClauseType::PutCode => {
                let mut stream = self.get_stream_or_alias(
                    self[temp_v!(1)],
                    &indices.stream_aliases,
                    "put_code",
                    2,
                )?;

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
                                if let Some(c) =
                                    u32::try_from(n).ok().and_then(|c| char::try_from(c).ok())
                                {
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
                        let err = MachineError::representation_error(RepFlag::CharacterCode);

                        return Err(self.error_form(err, stub));
                    }
                }
            }
            &SystemClauseType::PutChar => {
                let mut stream = self.get_stream_or_alias(
                    self[temp_v!(1)],
                    &indices.stream_aliases,
                    "put_char",
                    2,
                )?;

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
                            Addr::Con(h) if self.heap.atom_at(h) => match &self.heap[h] {
                                HeapCellValue::Atom(ref atom, _) if atom.is_char() => {
                                    if let Some(c) = atom.as_str().chars().next() {
                                        write!(&mut stream, "{}", c).unwrap();
                                        return return_from_clause!(self.last_call, self);
                                    } else {
                                        unreachable!()
                                    }
                                }
                                _ => {}
                            },
                            Addr::Char(c) => {
                                write!(&mut stream, "{}", c).unwrap();
                                return return_from_clause!(self.last_call, self);
                            }
                            _ => {}
                        }

                        let stub = MachineError::functor_stub(clause_name!("put_char"), 2);
                        let err =
                            MachineError::type_error(self.heap.h(), ValidType::Character, addr);

                        return Err(self.error_form(err, stub));
                    }
                }
            }
            &SystemClauseType::PutChars => {
                let mut stream = self.get_stream_or_alias(
                    self[temp_v!(1)],
                    &indices.stream_aliases,
                    "$put_chars",
                    2,
                )?;

                let mut bytes = Vec::new();
                let string = self.heap_pstr_iter(self[temp_v!(2)]).to_string();

                if stream.options().stream_type == StreamType::Binary {
                    for c in string.chars() {
                        if c as u32 > 255 {
                            let stub = MachineError::functor_stub(clause_name!("$put_chars"), 2);

                            let err = MachineError::type_error(
                                self.heap.h(),
                                ValidType::Byte,
                                Addr::Char(c),
                            );

                            return Err(self.error_form(err, stub));
                        }

                        bytes.push(c as u8);
                    }
                } else {
                    bytes = string.into_bytes();
                }

                match stream.write_all(&bytes) {
                    Ok(_) => {
                        return return_from_clause!(self.last_call, self);
                    }
                    _ => {
                        let stub = MachineError::functor_stub(clause_name!("$put_chars"), 2);

                        let addr = self
                            .heap
                            .to_unifiable(HeapCellValue::Stream(stream.clone()));

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
            &SystemClauseType::PutByte => {
                let mut stream = self.get_stream_or_alias(
                    self[temp_v!(1)],
                    &indices.stream_aliases,
                    "put_byte",
                    2,
                )?;

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
                            _ => {}
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
                let mut stream = self.get_stream_or_alias(
                    self[temp_v!(1)],
                    &indices.stream_aliases,
                    "get_byte",
                    2,
                )?;

                self.check_stream_properties(
                    &mut stream,
                    StreamType::Binary,
                    Some(self[temp_v!(2)]),
                    clause_name!("get_byte"),
                    2,
                )?;

                if stream.past_end_of_stream() {
                    self.eof_action(self[temp_v!(2)], &mut stream, clause_name!("get_byte"), 2)?;

                    if EOFAction::Reset != stream.options().eof_action {
                        return return_from_clause!(self.last_call, self);
                    } else if self.fail {
                        return Ok(());
                    }
                }

                let addr = match self.store(self.deref(self[temp_v!(2)])) {
                    addr if addr.is_ref() => addr,
                    addr => match Number::try_from((addr, &self.heap)) {
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
                    },
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
                            stream.set_past_end_of_stream();
                            (self.unify_fn)(self, self[temp_v!(2)], Addr::Fixnum(-1));
                            return return_from_clause!(self.last_call, self);
                        }
                    }
                }
            }
            &SystemClauseType::GetChar => {
                let mut stream = self.get_stream_or_alias(
                    self[temp_v!(1)],
                    &indices.stream_aliases,
                    "get_char",
                    2,
                )?;

                self.check_stream_properties(
                    &mut stream,
                    StreamType::Text,
                    Some(self[temp_v!(2)]),
                    clause_name!("get_char"),
                    2,
                )?;

                if stream.past_end_of_stream() {
                    if EOFAction::Reset != stream.options().eof_action {
                        return return_from_clause!(self.last_call, self);
                    } else if self.fail {
                        return Ok(());
                    }
                }

                if stream.at_end_of_stream() {
                    let end_of_file = clause_name!("end_of_file");
                    let end_of_file = self
                        .heap
                        .to_unifiable(HeapCellValue::Atom(end_of_file, None));

                    stream.set_past_end_of_stream();

                    (self.unify_fn)(self, self[temp_v!(2)], end_of_file);
                    return return_from_clause!(self.last_call, self);
                }

                let mut iter = self.open_parsing_stream(stream.clone(), "get_char", 2)?;

                let addr = match self.store(self.deref(self[temp_v!(2)])) {
                    addr if addr.is_ref() => addr,
                    Addr::Con(h) if self.heap.atom_at(h) => match &self.heap[h] {
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
                    },
                    Addr::Char(d) => Addr::Char(d),
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

                            if EOFAction::Reset != stream.options().eof_action {
                                return return_from_clause!(self.last_call, self);
                            } else if self.fail {
                                return Ok(());
                            }
                        } /*
                          _ => {
                              let stub = MachineError::functor_stub(clause_name!("get_char"), 2);
                              let err = MachineError::representation_error(RepFlag::Character);
                              let err = self.error_form(err, stub);

                              return Err(err);
                          }*/
                    }
                }
            }
            &SystemClauseType::GetNChars => {
                let stream = self.get_stream_or_alias(
                    self[temp_v!(1)],
                    &indices.stream_aliases,
                    "get_n_chars",
                    3,
                )?;

                let num = match Number::try_from((self[temp_v!(2)], &self.heap)) {
                    Ok(Number::Fixnum(n)) => usize::try_from(n).unwrap(),
                    Ok(Number::Integer(n)) => match n.to_usize() {
                        Some(u) => u,
                        _ => {
                            self.fail = true;
                            return Ok(());
                        }
                    },
                    _ => {
                        unreachable!()
                    }
                };

                let mut string = String::new();

                if stream.options().stream_type == StreamType::Binary {
                    let mut buf = vec![];
                    let mut chunk = stream.take(num as u64);
                    chunk.read_to_end(&mut buf).ok();
                    for c in buf {
                        string.push(c as char);
                    }
                } else {
                    let mut iter = self.open_parsing_stream(stream.clone(), "get_n_chars", 2)?;

                    for _ in 0..num {
                        let result = iter.next();

                        match result {
                            Some(Ok(c)) => {
                                string.push(c);
                            }
                            _ => {
                                break;
                            }
                        }
                    }
                };
                let string = self.heap.put_complete_string(&string);
                (self.unify_fn)(self, self[temp_v!(3)], string);
            }
            &SystemClauseType::GetCode => {
                let mut stream = self.get_stream_or_alias(
                    self[temp_v!(1)],
                    &indices.stream_aliases,
                    "get_code",
                    2,
                )?;

                self.check_stream_properties(
                    &mut stream,
                    StreamType::Text,
                    Some(self[temp_v!(2)]),
                    clause_name!("get_code"),
                    2,
                )?;

                if stream.past_end_of_stream() {
                    if EOFAction::Reset != stream.options().eof_action {
                        return return_from_clause!(self.last_call, self);
                    } else if self.fail {
                        return Ok(());
                    }
                }

                if stream.at_end_of_stream() {
                    let end_of_file = clause_name!("end_of_file");
                    let end_of_file = self
                        .heap
                        .to_unifiable(HeapCellValue::Atom(end_of_file, None));

                    stream.set_past_end_of_stream();

                    (self.unify_fn)(self, self[temp_v!(2)], end_of_file);
                    return return_from_clause!(self.last_call, self);
                }

                let addr = match self.store(self.deref(self[temp_v!(2)])) {
                    addr if addr.is_ref() => addr,
                    addr => match Number::try_from((addr, &self.heap)) {
                        Ok(Number::Integer(n)) => {
                            let n = n
                                .to_u32()
                                .and_then(|n| std::char::from_u32(n).and_then(|_| Some(n)));

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
                            let n = u32::try_from(n)
                                .ok()
                                .and_then(|n| std::char::from_u32(n).and_then(|_| Some(n)));

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
                    },
                };

                let mut iter = self.open_parsing_stream(stream.clone(), "get_code", 2)?;

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

                            if EOFAction::Reset != stream.options().eof_action {
                                return return_from_clause!(self.last_call, self);
                            } else if self.fail {
                                return Ok(());
                            }
                        }
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
                let prev_stream = match self.store(self.deref(self[temp_v!(1)])) {
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

                let mut next_stream = None;
                let mut null_streams = BTreeSet::new();

                for stream in indices
                    .streams
                    .range(prev_stream.clone()..)
                    .skip(1)
                    .cloned()
                {
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
                let mut stream = self.get_stream_or_alias(
                    self[temp_v!(1)],
                    &indices.stream_aliases,
                    "flush_output",
                    1,
                )?;

                if !stream.is_output_stream() {
                    let stub = MachineError::functor_stub(clause_name!("flush_output"), 1);

                    let addr = vec![HeapCellValue::Stream(stream)];

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
                    modifiers: KeyModifiers::CONTROL,
                };
                let key = get_key();
                if key == ctrl_c {
                    let stub = MachineError::functor_stub(clause_name!("get_single_char"), 1);
                    let err = MachineError::interrupt_error();
                    let err = self.error_form(err, stub);

                    return Err(err);
                }
                let c = match key.code {
                    KeyCode::Enter => '\n',
                    KeyCode::Tab => '\t',
                    KeyCode::Char(c) => c,
                    _ => unreachable!(),
                };

                let a1 = self[temp_v!(1)];

                (self.unify_fn)(self, Addr::Char(c), a1);
            }
            &SystemClauseType::HeadIsDynamic => {
                let module_name = atom_from!(self, self.store(self.deref(self[temp_v!(1)])));

                self.fail = !match self.store(self.deref(self[temp_v!(2)])) {
                    Addr::Str(s) => match &self.heap[s] {
                        &HeapCellValue::NamedStr(arity, ref name, ..) => {
                            indices.is_dynamic_predicate(module_name, (name.clone(), arity))
                        }
                        _ => unreachable!(),
                    },
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(name, _) = &self.heap[h] {
                            indices.is_dynamic_predicate(module_name, (name.clone(), 0))
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
                let mut stream = self.get_stream_or_alias(
                    self[temp_v!(1)],
                    &indices.stream_aliases,
                    "close",
                    2,
                )?;

                if !stream.is_input_stream() {
                    stream.flush().unwrap(); // 8.11.6.1b)
                }

                indices.streams.remove(&stream);

                if stream == *current_input_stream {
                    *current_input_stream = indices
                        .stream_aliases
                        .get(&clause_name!("user_input"))
                        .cloned()
                        .unwrap();

                    indices.streams.insert(current_input_stream.clone());
                } else if stream == *current_output_stream {
                    *current_output_stream = indices
                        .stream_aliases
                        .get(&clause_name!("user_output"))
                        .cloned()
                        .unwrap();

                    indices.streams.insert(current_output_stream.clone());
                }

                if !stream.is_stdin() && !stream.is_stdout() && !stream.is_stderr() {
                    stream.close();

                    if let Some(ref alias) = stream.options().alias {
                        indices.stream_aliases.remove(alias);
                    }
                }
            }
            &SystemClauseType::CopyToLiftedHeap => match self.store(self.deref(self[temp_v!(1)])) {
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
            },
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
                            _ => unreachable!(),
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
                            for i in (arity + 1..arity + narity + 1).rev() {
                                self.registers[i] = self.registers[i - arity];
                            }

                            for i in 1..arity + 1 {
                                self.registers[i] = self.heap[a + i].as_addr(a + i);
                            }

                            return self.module_lookup(
                                indices,
                                call_policy,
                                (name, arity + narity),
                                module_name,
                                true,
                                &indices.stream_aliases,
                            );
                        } else {
                            unreachable!()
                        }
                    }
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(name, _) = self.heap.clone(h) {
                            return self.module_lookup(
                                indices,
                                call_policy,
                                (name.clone(), narity),
                                module_name,
                                true,
                                &indices.stream_aliases,
                            );
                        } else {
                            unreachable!()
                        }
                    }
                    Addr::Char(c) => {
                        return self.module_lookup(
                            indices,
                            call_policy,
                            (clause_name!(c.to_string(), self.atom_tbl), narity),
                            module_name,
                            true,
                            &indices.stream_aliases,
                        );
                    }
                    addr => {
                        let stub = MachineError::functor_stub(clause_name!("(:)"), 2);

                        let type_error =
                            MachineError::type_error(self.heap.h(), ValidType::Callable, addr);

                        let type_error = self.error_form(type_error, stub);
                        return Err(type_error);
                    }
                }
            }
            &SystemClauseType::EnqueueAttributedVar => {
                let addr = self[temp_v!(1)];

                match self.store(self.deref(addr)) {
                    Addr::AttrVar(h) => {
                        self.attr_var_init.attr_var_queue.push(h);
                    }
                    _ => {}
                }
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
                                &CompositeOpDir::new(&indices.op_dir, None),
                            );

                            let db_ref = DBRef::NamedPred(name.clone(), *arity, spec);
                            let r = addr.as_var().unwrap();

                            let addr = self.heap.to_unifiable(HeapCellValue::DBRef(db_ref));

                            self.bind(r, addr);

                            return return_from_clause!(self.last_call, self);
                        }

                        self.fail = true;
                    }
                    Addr::Con(h) => match self.heap.clone(h) {
                        HeapCellValue::DBRef(DBRef::Op(..)) => {
                            self.fail = true;
                        }
                        HeapCellValue::DBRef(ref db_ref) => {
                            self.get_next_db_ref(indices, db_ref);
                        }
                        _ => {
                            self.fail = true;
                        }
                    },
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
                                let addr = self.heap.to_unifiable(HeapCellValue::DBRef(db_ref));

                                self.bind(r, addr);
                            }
                            None => {
                                self.fail = true;
                                return Ok(());
                            }
                        }
                    }
                    Addr::Con(h) => match self.heap.clone(h) {
                        HeapCellValue::DBRef(DBRef::NamedPred(..)) => {
                            self.fail = true;
                        }
                        HeapCellValue::DBRef(ref db_ref) => {
                            self.get_next_db_ref(indices, db_ref);
                        }
                        _ => {
                            self.fail = true;
                        }
                    },
                    _ => {
                        self.fail = true;
                    }
                }
            }
            &SystemClauseType::LookupDBRef => {
                let a1 = self[temp_v!(1)];

                match self.store(self.deref(a1)) {
                    Addr::Con(h) => match self.heap.clone(h) {
                        HeapCellValue::DBRef(DBRef::NamedPred(name, arity, spec)) => {
                            let a2 = self[temp_v!(2)];
                            let a3 = self[temp_v!(3)];

                            let atom = self.heap.to_unifiable(HeapCellValue::Atom(name, spec));

                            (self.unify_fn)(self, a2, atom);

                            if !self.fail {
                                (self.unify_fn)(self, a3, Addr::Usize(arity));
                            }
                        }
                        _ => {
                            self.fail = true;
                        }
                    },
                    _ => {
                        self.fail = true;
                    }
                }
            }
            &SystemClauseType::LookupOpDBRef => {
                let a1 = self[temp_v!(1)];

                match self.store(self.deref(a1)) {
                    Addr::Con(h) => match self.heap.clone(h) {
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

                            let a3 = self
                                .heap
                                .to_unifiable(HeapCellValue::Atom(clause_name!(spec), None));

                            let a4 = self
                                .heap
                                .to_unifiable(HeapCellValue::Atom(name, Some(shared_op_desc)));

                            (self.unify_fn)(self, Addr::Usize(priority), prec);

                            if !self.fail {
                                (self.unify_fn)(self, a3, specifier);
                            }

                            if !self.fail {
                                (self.unify_fn)(self, a4, op);
                            }
                        }
                        _ => {
                            self.fail = true;
                        }
                    },
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

                (self.unify_fn)(self, a1, addr);
            }
            &SystemClauseType::CurrentTime => {
                let str = self.systemtime_to_timestamp(SystemTime::now());
                (self.unify_fn)(self, self[temp_v!(1)], str);
            }
            &SystemClauseType::OpDeclaration => {
                let priority = self[temp_v!(1)];
                let specifier = self[temp_v!(2)];
                let op = self[temp_v!(3)];

                let priority = self.store(self.deref(priority));

                let priority = match Number::try_from((priority, &self.heap)) {
                    Ok(Number::Integer(n)) => n.to_usize().unwrap(),
                    Ok(Number::Fixnum(n)) => usize::try_from(n).unwrap(),
                    _ => {
                        unreachable!();
                    }
                };

                let specifier = match self.store(self.deref(specifier)) {
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(ref specifier, _) = &self.heap[h] {
                            specifier.clone()
                        } else {
                            unreachable!()
                        }
                    }
                    _ => unreachable!(),
                };

                let op = match self.store(self.deref(op)) {
                    Addr::Char(c) => clause_name!(c.to_string(), self.atom_tbl),
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(ref name, _) = &self.heap[h] {
                            name.clone()
                        } else {
                            unreachable!()
                        }
                    }
                    _ => unreachable!(),
                };

                let result = to_op_decl(priority, specifier.as_str(), op)
                    .map_err(SessionError::from)
                    .and_then(|mut op_decl| {
                        if op_decl.prec == 0 {
                            Ok(op_decl.remove(&mut indices.op_dir))
                        } else {
                            let spec = get_op_desc(
                                op_decl.name.clone(),
                                &CompositeOpDir::new(&indices.op_dir, None),
                            );

                            op_decl.submit(spec, &mut indices.op_dir)
                        }
                    });

                match result {
                    Ok(()) => {}
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

                let options = self.to_stream_options(alias, eof_action, reposition, stream_type);

                let mut stream = match self.store(self.deref(self[temp_v!(1)])) {
                    Addr::Con(h) if self.heap.atom_at(h) => match &self.heap[h] {
                        &HeapCellValue::Atom(ref atom, _) => {
                            self.stream_from_file_spec(atom.clone(), indices, &options)?
                        }
                        _ => {
                            unreachable!()
                        }
                    },
                    Addr::Char(c) => {
                        let atom = clause_name!(c.to_string(), self.atom_tbl);
                        self.stream_from_file_spec(atom, indices, &options)?
                    }
                    Addr::PStrLocation(h, n) => match &self.heap[h] {
                        &HeapCellValue::PartialString(_, _has_tail @ false) => {
                            let mut heap_pstr_iter = self.heap_pstr_iter(Addr::PStrLocation(h, n));

                            let file_spec = clause_name!(heap_pstr_iter.to_string(), self.atom_tbl);

                            self.stream_from_file_spec(file_spec, indices, &options)?
                        }
                        _ => self.stream_from_file_spec(clause_name!(""), indices, &options)?,
                    },
                    _ => self.stream_from_file_spec(clause_name!(""), indices, &options)?,
                };

                *stream.options_mut() = options;

                indices.streams.insert(stream.clone());

                if let Some(ref alias) = &stream.options().alias {
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
            &SystemClauseType::GetAttributedVariableList => {
                let attr_var = self.store(self.deref(self[temp_v!(1)]));
                let attr_var_list = match attr_var {
                    Addr::AttrVar(h) => h + 1,
                    attr_var @ Addr::HeapCell(_) | attr_var @ Addr::StackCell(..) => {
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

                (self.unify_fn)(self, addr, value);
            }
            &SystemClauseType::GetAttrVarQueueBeyond => {
                let addr = self[temp_v!(1)];
                let addr = self.store(self.deref(addr));

                let b = match addr {
                    Addr::Usize(b) => Some(b),
                    _ => match Number::try_from((addr, &self.heap)) {
                        Ok(Number::Integer(n)) => n.to_usize(),
                        Ok(Number::Fixnum(n)) => usize::try_from(n).ok(),
                        _ => {
                            self.fail = true;
                            return Ok(());
                        }
                    },
                };

                if let Some(b) = b {
                    let iter = self.gather_attr_vars_created_since(b);

                    let var_list_addr = Addr::HeapCell(self.heap.to_list(iter));
                    let list_addr = self[temp_v!(2)];

                    (self.unify_fn)(self, var_list_addr, list_addr);
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

                let num_cells = match code_repo.lookup_instr(self.last_call, &CodePtr::Local(p)) {
                    Some(line) => {
                        let perm_vars = match line.as_ref() {
                            Line::Control(ref ctrl_instr) => ctrl_instr.perm_vars(),
                            _ => None,
                        };

                        perm_vars.unwrap()
                    }
                    _ => unreachable!(),
                };

                let mut addrs = vec![];

                for index in 1..num_cells + 1 {
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

                (self.unify_fn)(self, self[temp_v!(3)], chunk);
            }
            &SystemClauseType::GetLiftedHeapFromOffsetDiff => {
                let lh_offset = self[temp_v!(1)];

                match self.store(self.deref(lh_offset)) {
                    Addr::Usize(lh_offset) => {
                        if lh_offset >= self.lifted_heap.h() {
                            let solutions = self[temp_v!(2)];
                            let diff = self[temp_v!(3)];

                            (self.unify_fn)(self, solutions, diff);
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
                                    (self.unify_fn)(self, diff, addr);
                                });
                            }

                            self.lifted_heap.truncate(lh_offset);

                            let solutions = self[temp_v!(2)];
                            (self.unify_fn)(self, Addr::HeapCell(h), solutions);
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
                            (self.unify_fn)(self, solutions, Addr::EmptyList);
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
                            (self.unify_fn)(self, Addr::HeapCell(h), solutions);
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
                        let atom = self
                            .heap
                            .to_unifiable(HeapCellValue::Atom(clause_name!("chars"), None));

                        (self.unify_fn)(self, a1, atom);
                    }
                    DoubleQuotes::Atom => {
                        let atom = self
                            .heap
                            .to_unifiable(HeapCellValue::Atom(clause_name!("atom"), None));

                        (self.unify_fn)(self, a1, atom);
                    }
                    DoubleQuotes::Codes => {
                        let atom = self
                            .heap
                            .to_unifiable(HeapCellValue::Atom(clause_name!("codes"), None));

                        (self.unify_fn)(self, a1, atom);
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
                    None => {}
                };

                self.fail = true;
            }
            &SystemClauseType::Halt => {
                let code = self.store(self.deref(self[temp_v!(1)]));

                let code = match Number::try_from((code, &self.heap)) {
                    Ok(Number::Fixnum(n)) => n as i32,
                    Ok(Number::Integer(n)) => n.to_i32().unwrap(),
                    Ok(Number::Rational(r)) => {
                        // n has already been confirmed as an integer, and
                        // internally, Rational is assumed reduced, so its
                        // denominator must be 1.
                        r.numer().to_i32().unwrap()
                    }
                    _ => {
                        unreachable!()
                    }
                };

                std::process::exit(code);
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

                let n = match Number::try_from((a2, &self.heap)) {
                    Ok(Number::Integer(n)) => Integer::from(&*n.clone()),
                    Ok(Number::Fixnum(n)) => Integer::from(n),
                    _ => {
                        let stub = MachineError::functor_stub(
                            clause_name!("call_with_inference_limit"),
                            3,
                        );

                        return Err(self.error_form(
                            MachineError::type_error(self.heap.h(), ValidType::Integer, a2),
                            stub,
                        ));
                    }
                };

                match a1 {
                    Addr::Usize(bp) | Addr::CutPoint(bp) => {
                        match call_policy.downcast_mut::<CWILCallPolicy>().ok() {
                            Some(call_policy) => {
                                let count = call_policy.add_limit(n, bp).clone();
                                let count = self
                                    .heap
                                    .to_unifiable(HeapCellValue::Integer(Rc::new(count)));

                                let a3 = self[temp_v!(3)];
                                (self.unify_fn)(self, a3, count);
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
            &SystemClauseType::NoSuchPredicate => {
                let module_name = atom_from!(self, self.store(self.deref(self[temp_v!(1)])));

                self.fail = match self.store(self.deref(self[temp_v!(2)])) {
                    Addr::Str(s) => match &self.heap[s] {
                        &HeapCellValue::NamedStr(arity, ref name, ref spec) => {
                            if CLAUSE_TYPE_FORMS
                                .borrow()
                                .get(&(name.as_str(), arity))
                                .is_some()
                            {
                                true
                            } else {
                                let index = indices
                                    .get_predicate_code_index(
                                        name.clone(),
                                        arity,
                                        module_name,
                                        spec.clone(),
                                    )
                                    .map(|index| index.get())
                                    .unwrap_or(IndexPtr::DynamicUndefined);

                                match index {
                                    IndexPtr::DynamicUndefined => false,
                                    _ => true,
                                }
                            }
                        }
                        _ => {
                            unreachable!()
                        }
                    },
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let &HeapCellValue::Atom(ref name, ref spec) = &self.heap[h] {
                            let spec =
                                fetch_atom_op_spec(name.clone(), spec.clone(), &indices.op_dir);

                            if CLAUSE_TYPE_FORMS
                                .borrow()
                                .get(&(name.as_str(), 0))
                                .is_some()
                            {
                                true
                            } else {
                                let index = indices
                                    .get_predicate_code_index(
                                        name.clone(),
                                        0,
                                        module_name,
                                        spec.clone(),
                                    )
                                    .map(|index| index.get())
                                    .unwrap_or(IndexPtr::DynamicUndefined);

                                match index {
                                    IndexPtr::DynamicUndefined => false,
                                    _ => true,
                                }
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    head => {
                        let err =
                            MachineError::type_error(self.heap.h(), ValidType::Callable, head);
                        let stub = MachineError::functor_stub(clause_name!("clause"), 2);

                        return Err(self.error_form(err, stub));
                    }
                };
            }
            &SystemClauseType::RedoAttrVarBinding => {
                let var = self.store(self.deref(self[temp_v!(1)]));
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
            &SystemClauseType::ResetAttrVarState => {
                self.attr_var_init.reset();
            }
            &SystemClauseType::RemoveCallPolicyCheck => {
                let restore_default = match call_policy.downcast_mut::<CWILCallPolicy>().ok() {
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
                                let count = self
                                    .heap
                                    .to_unifiable(HeapCellValue::Integer(Rc::new(count)));

                                let a2 = self[temp_v!(2)];

                                (self.unify_fn)(self, a2, count);
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
            &SystemClauseType::ReturnFromVerifyAttr => {
                let e = self.e;
                let frame_len = self.stack.index_and_frame(e).prelude.univ_prelude.num_cells;

                for i in 1..frame_len - 1 {
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
            &SystemClauseType::SetCutPointByDefault(r) => deref_cut(self, r),
            &SystemClauseType::SetInput => {
                let addr = self.store(self.deref(self[temp_v!(1)]));
                let stream =
                    self.get_stream_or_alias(addr, &indices.stream_aliases, "set_input", 1)?;

                if !stream.is_input_stream() {
                    let stub = MachineError::functor_stub(clause_name!("set_input"), 1);

                    let user_alias = self
                        .heap
                        .to_unifiable(HeapCellValue::Atom(clause_name!("user"), None));

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
                let stream =
                    self.get_stream_or_alias(addr, &indices.stream_aliases, "set_output", 1)?;

                if !stream.is_output_stream() {
                    let stub = MachineError::functor_stub(clause_name!("set_input"), 1);

                    let user_alias = self
                        .heap
                        .to_unifiable(HeapCellValue::Atom(clause_name!("user"), None));

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
            &SystemClauseType::SetDoubleQuotes => match self[temp_v!(1)] {
                Addr::Con(h) if self.heap.atom_at(h) => {
                    if let HeapCellValue::Atom(ref atom, _) = &self.heap[h] {
                        self.flags.double_quotes = match atom.as_str() {
                            "atom" => DoubleQuotes::Atom,
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
            },
            &SystemClauseType::InferenceLevel => {
                let a1 = self[temp_v!(1)];
                let a2 = self.store(self.deref(self[temp_v!(2)]));

                match a2 {
                    Addr::CutPoint(bp) | Addr::Usize(bp) => {
                        let prev_b = self.stack.index_or_frame(self.b).prelude.b;

                        if prev_b <= bp {
                            let a2 = self
                                .heap
                                .to_unifiable(HeapCellValue::Atom(clause_name!("!"), None));

                            (self.unify_fn)(self, a1, a2);
                        } else {
                            let a2 = self
                                .heap
                                .to_unifiable(HeapCellValue::Atom(clause_name!("true"), None));

                            (self.unify_fn)(self, a1, a2);
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

                (self.unify_fn)(self, a1, a2);
            }
            &SystemClauseType::GetCutPoint => {
                let a1 = self[temp_v!(1)];
                let a2 = Addr::CutPoint(self.b0);

                (self.unify_fn)(self, a1, a2);
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

                                let cp =
                                    (self.stack.index_and_frame(self.e).prelude.cp - 1).unwrap();

                                let e = self.stack.index_and_frame(self.e).prelude.e;
                                let e = Addr::Usize(e);

                                let p = cp.as_functor(&mut self.heap);

                                (self.unify_fn)(self, self[temp_v!(2)], e);

                                if !self.fail {
                                    (self.unify_fn)(self, self[temp_v!(3)], p);
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

                        (self.unify_fn)(self, self[temp_v!(2)], e);

                        if !self.fail {
                            (self.unify_fn)(self, self[temp_v!(3)], p);
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
                    Some(p) => p + 1,
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
                            Some(c) => non_quoted_token(once(c)),
                            None => true,
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
                    Ok(()) => {}
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
                    &indices.stream_aliases,
                    "read_term",
                    3,
                )?;

                self.read_term(stream, indices)?;
            }
            &SystemClauseType::ReadTermFromChars => {
                let mut heap_pstr_iter = self.heap_pstr_iter(self[temp_v!(1)]);
                let chars = heap_pstr_iter.to_string();

                if let Addr::EmptyList = heap_pstr_iter.focus() {
                    let term_write_result = match self.read(
                        Stream::from(chars),
                        self.atom_tbl.clone(),
                        &indices.op_dir,
                    ) {
                        Ok(term_write_result) => term_write_result,
                        Err(e) => {
                            let stub =
                                MachineError::functor_stub(clause_name!("read_term_from_chars"), 2);

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
                self[temp_v!(3)] = self
                    .heap
                    .to_unifiable(HeapCellValue::Atom(clause_name!("none"), None));

                let h = self.heap.h();

                self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
                self[temp_v!(4)] = Addr::HeapCell(h);
            }
            &SystemClauseType::SetBall => {
                self.set_ball();
            }
            &SystemClauseType::SetSeed => {
                let seed = self.store(self.deref(self[temp_v!(1)]));

                let seed = match Number::try_from((seed, &self.heap)) {
                    Ok(Number::Fixnum(n)) => Integer::from(n),
                    Ok(Number::Integer(n)) => Integer::from(n.as_ref()),
                    Ok(Number::Rational(n)) if n.denom() == &1 => n.numer().clone(),
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                };

                let mut rand = RANDOM_STATE.borrow_mut();
                rand.seed(&seed);
            }
            &SystemClauseType::SkipMaxList => {
                if let Err(err) = self.skip_max_list() {
                    return Err(err);
                }
            }
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

                let socket_atom = match addr {
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

                let port = match port {
                    Addr::Fixnum(n) => n.to_string(),
                    Addr::Usize(n) => n.to_string(),
                    Addr::Con(h) => match &self.heap[h] {
                        HeapCellValue::Atom(ref name, _) => name.as_str().to_string(),
                        HeapCellValue::Integer(ref n) => n.to_string(),
                        _ => {
                            unreachable!()
                        }
                    },
                    _ => {
                        unreachable!()
                    }
                };

                let socket_addr = format!(
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

                let options = self.to_stream_options(alias, eof_action, reposition, stream_type);

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

                let stream = match TcpStream::connect(&socket_addr).map_err(|e| e.kind()) {
                    Ok(tcp_stream) => {
                        let socket_addr = clause_name!(socket_addr, self.atom_tbl);

                        let mut stream = {
                            let tls = match self.store(self.deref(self[temp_v!(8)])) {
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

                            match tls {
                                "false" => Stream::from_tcp_stream(socket_addr, tcp_stream),
                                "true" => {
                                    let connector = TlsConnector::new().unwrap();
                                    let stream =
                                        match connector.connect(socket_atom.as_str(), tcp_stream) {
                                            Ok(tls_stream) => tls_stream,
                                            Err(_) => {
                                                return Err(self.open_permission_error(
                                                    addr,
                                                    "socket_client_open",
                                                    3,
                                                ));
                                            }
                                        };

                                    Stream::from_tls_stream(socket_addr, stream)
                                }
                                _ => {
                                    unreachable!()
                                }
                            }
                        };

                        *stream.options_mut() = options;

                        if let Some(ref alias) = &stream.options().alias {
                            indices.stream_aliases.insert(alias.clone(), stream.clone());
                        }

                        indices.streams.insert(stream.clone());

                        self.heap.to_unifiable(HeapCellValue::Stream(stream))
                    }
                    Err(ErrorKind::PermissionDenied) => {
                        return Err(self.open_permission_error(addr, "socket_client_open", 3));
                    }
                    Err(ErrorKind::NotFound) => {
                        let stub =
                            MachineError::functor_stub(clause_name!("socket_client_open"), 3);

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
                let socket_atom = match addr {
                    Addr::EmptyList => "127.0.0.1".to_string(),
                    Addr::Con(h) if self.heap.atom_at(h) => match &self.heap[h] {
                        HeapCellValue::Atom(ref name, _) => name.as_str().to_string(),
                        _ => {
                            unreachable!()
                        }
                    },
                    _ => {
                        unreachable!()
                    }
                };

                let port = match self.store(self.deref(self[temp_v!(2)])) {
                    Addr::Fixnum(n) => n.to_string(),
                    Addr::Usize(n) => n.to_string(),
                    Addr::Con(h) => match &self.heap[h] {
                        HeapCellValue::Integer(ref n) => n.to_string(),
                        _ => {
                            unreachable!()
                        }
                    },
                    addr if addr.is_ref() => "0".to_string(),
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
                                    self.heap
                                        .to_unifiable(HeapCellValue::TcpListener(tcp_listener)),
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
                    (self.unify_fn)(self, self[temp_v!(2)], Addr::Usize(port));
                }
            }
            &SystemClauseType::SocketServerAccept => {
                let alias = self[temp_v!(4)];
                let eof_action = self[temp_v!(5)];
                let reposition = self[temp_v!(6)];
                let stream_type = self[temp_v!(7)];

                let options = self.to_stream_options(alias, eof_action, reposition, stream_type);

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
                    Addr::TcpListener(h) => match &mut self.heap[h] {
                        HeapCellValue::TcpListener(ref mut tcp_listener) => {
                            match tcp_listener.accept().ok() {
                                Some((tcp_stream, socket_addr)) => {
                                    let client =
                                        clause_name!(format!("{}", socket_addr), self.atom_tbl);

                                    let mut tcp_stream =
                                        Stream::from_tcp_stream(client.clone(), tcp_stream);

                                    *tcp_stream.options_mut() = options;

                                    if let Some(ref alias) = &tcp_stream.options().alias {
                                        indices
                                            .stream_aliases
                                            .insert(alias.clone(), tcp_stream.clone());
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
                    },
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
                    &indices.stream_aliases,
                    "set_stream_position",
                    2,
                )?;

                if !stream.options().reposition {
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

                let position = match Number::try_from((position, &self.heap)) {
                    Ok(Number::Fixnum(n)) => n as u64,
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
                    &indices.stream_aliases,
                    "stream_property",
                    2,
                )?;

                let property = match self.store(self.deref(self[temp_v!(2)])) {
                    Addr::Con(h) if self.heap.atom_at(h) => match &self.heap[h] {
                        HeapCellValue::Atom(ref name, _) => match name.as_str() {
                            "file_name" => {
                                if let Some(file_name) = stream.file_name() {
                                    HeapCellValue::Atom(file_name, None)
                                } else {
                                    self.fail = true;
                                    return Ok(());
                                }
                            }
                            "mode" => HeapCellValue::Atom(clause_name!(stream.mode()), None),
                            "direction" => HeapCellValue::Atom(
                                if stream.is_input_stream() && stream.is_output_stream() {
                                    clause_name!("input_output")
                                } else if stream.is_input_stream() {
                                    clause_name!("input")
                                } else {
                                    clause_name!("output")
                                },
                                None,
                            ),
                            "alias" => {
                                if let Some(alias) = &stream.options().alias {
                                    HeapCellValue::Atom(alias.clone(), None)
                                } else {
                                    self.fail = true;
                                    return Ok(());
                                }
                            }
                            "position" => {
                                if let Some((position, lines_read)) = stream.position() {
                                    let h = self.heap.h();

                                    let position_term = functor!(
                                        "position_and_lines_read",
                                        [integer(position), integer(lines_read)]
                                    );

                                    self.heap.extend(position_term.into_iter());

                                    HeapCellValue::Addr(Addr::HeapCell(h))
                                } else {
                                    self.fail = true;
                                    return Ok(());
                                }
                            }
                            "end_of_stream" => {
                                let end_of_stream_pos = stream.position_relative_to_end();
                                HeapCellValue::Atom(clause_name!(end_of_stream_pos.as_str()), None)
                            }
                            "eof_action" => HeapCellValue::Atom(
                                clause_name!(stream.options().eof_action.as_str()),
                                None,
                            ),
                            "reposition" => HeapCellValue::Atom(
                                clause_name!(if stream.options().reposition {
                                    "true"
                                } else {
                                    "false"
                                }),
                                None,
                            ),
                            "type" => HeapCellValue::Atom(
                                clause_name!(stream.options().stream_type.as_property_str()),
                                None,
                            ),
                            _ => {
                                unreachable!()
                            }
                        },
                        _ => {
                            unreachable!()
                        }
                    },
                    _ => {
                        unreachable!()
                    }
                };

                let property = self.heap.to_unifiable(property);
                (self.unify_fn)(self, self[temp_v!(3)], property);
            }
            &SystemClauseType::StoreGlobalVar => {
                let key = match self.store(self.deref(self[temp_v!(1)])) {
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
            &SystemClauseType::StoreBacktrackableGlobalVar => {
                let (key_h, key) = match self.store(self.deref(self[temp_v!(1)])) {
                    Addr::Con(h) if self.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(ref atom, _) = &self.heap[h] {
                            (h, atom.clone())
                        } else {
                            unreachable!()
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                };

                let new_value = self.store(self.deref(self[temp_v!(2)]));

                match indices.global_variables.get_mut(&key) {
                    Some((_, ref mut loc)) => match loc {
                        Some(ref mut value) => {
                            let old_value_loc = self.heap.push(HeapCellValue::Addr(*value));
                            self.trail(TrailRef::BlackboardOffset(key_h, old_value_loc));
                            *value = new_value;
                        }
                        loc @ None => {
                            self.trail(TrailRef::BlackboardEntry(key_h));
                            *loc = Some(new_value);
                        }
                    },
                    None => {
                        self.trail(TrailRef::BlackboardEntry(key_h));
                        indices
                            .global_variables
                            .insert(key, (Ball::new(), Some(new_value)));
                    }
                }
            }
            &SystemClauseType::Succeed => {}
            &SystemClauseType::TermAttributedVariables => {
                let seen_vars = self.attr_vars_of_term(self[temp_v!(1)]);
                let outcome = Addr::HeapCell(self.heap.to_list(seen_vars.into_iter()));

                (self.unify_fn)(self, self[temp_v!(2)], outcome);
            }
            &SystemClauseType::TermVariables => {
                let a1 = self[temp_v!(1)];
                let mut seen_set = IndexSet::new();
                let mut seen_vars = vec![];

                for addr in self.acyclic_pre_order_iter(a1) {
                    if addr.is_ref() && !seen_set.contains(&addr) {
                        seen_vars.push(addr);
                        seen_set.insert(addr);
                    }
                }

                let outcome = Addr::HeapCell(self.heap.to_list(seen_vars.into_iter()));
                (self.unify_fn)(self, self[temp_v!(2)], outcome);
            }
            &SystemClauseType::TruncateLiftedHeapTo => {
                match self.store(self.deref(self[temp_v!(1)])) {
                    Addr::Usize(lh_offset) => self.lifted_heap.truncate(lh_offset),
                    _ => self.fail = true,
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
                let module_name = atom_from!(self, self.store(self.deref(self[temp_v!(1)])));

                let name = self[temp_v!(2)];
                let arity = self[temp_v!(3)];

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

                let arity = match Number::try_from((arity, &self.heap)) {
                    Ok(Number::Fixnum(n)) => Integer::from(n),
                    Ok(Number::Integer(n)) => Integer::from(n.as_ref()),
                    _ => {
                        unreachable!()
                    }
                };

                let key = (name.clone(), arity.to_usize().unwrap());

                let first_idx = match module_name.as_str() {
                    "user" => indices.code_dir.get(&key),
                    _ => match indices.modules.get(&module_name) {
                        Some(module) => module.code_dir.get(&key),
                        None => {
                            let stub = MachineError::functor_stub(key.0, key.1);
                            let h = self.heap.h();

                            let err = MachineError::session_error(
                                h,
                                SessionError::from(CompilationError::InvalidModuleResolution(
                                    module_name,
                                )),
                            );

                            let err = self.error_form(err, stub);

                            self.throw_exception(err);
                            return Ok(());
                        }
                    },
                };

                let first_idx = match first_idx {
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
                let mut functor_list = vec![];

                walk_code(&code_repo.code, first_idx, |instr| {
                    let old_len = functors.len();
                    instr.enqueue_functors(h, &mut functors);
                    let new_len = functors.len();

                    for index in old_len..new_len {
                        functor_list.push(Addr::HeapCell(h));
                        h += functors[index].len();
                    }
                });

                for functor in functors {
                    self.heap.extend(functor.into_iter());
                }

                let listing = Addr::HeapCell(self.heap.to_list(functor_list.into_iter()));
                let listing_var = self[temp_v!(4)];

                (self.unify_fn)(self, listing, listing_var);
            }
            &SystemClauseType::WriteTerm => {
                let mut stream = self.get_stream_or_alias(
                    self[temp_v!(1)],
                    &indices.stream_aliases,
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

                let opt_err = if !stream.is_output_stream() {
                    Some("stream") // 8.14.2.3 g)
                } else if stream.options().stream_type == StreamType::Binary {
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

                let printer = match self.write_term(&indices.op_dir)? {
                    None => {
                        self.fail = true;
                        return Ok(());
                    }
                    Some(printer) => printer,
                };

                let output = printer.print(addr);

                match write!(&mut stream, "{}", output.result()) {
                    Ok(_) => {}
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

                let printer = match self.write_term(&indices.op_dir)? {
                    None => {
                        self.fail = true;
                        return Ok(());
                    }
                    Some(printer) => printer,
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
                use git_version::git_version;
                let version = self[temp_v!(1)];
                let buffer = git_version!(cargo_prefix = "cargo:", fallback = "unknown");
                let chars = buffer.chars().map(|c| Addr::Char(c));
                let result = Addr::HeapCell(self.heap.to_list(chars));
                (self.unify_fn)(self, version, result);
            }
            &SystemClauseType::CryptoRandomByte => {
                let arg = self[temp_v!(1)];
                let mut bytes: [u8; 1] = [0];

                match rng().fill(&mut bytes) {
                    Ok(()) => {}
                    Err(_) => {
                        // the error payload here is of type 'Unspecified',
                        // which contains no information whatsoever. So, for now,
                        // just fail.
                        self.fail = true;
                        return Ok(());
                    }
                }

                let byte = self
                    .heap
                    .to_unifiable(HeapCellValue::Integer(Rc::new(Integer::from(bytes[0]))));

                (self.unify_fn)(self, arg, byte);
            }
            &SystemClauseType::CryptoDataHash => {
                let encoding = self.atom_argument_to_string(2);
                let bytes = self.string_encoding_bytes(1, &encoding);

                let algorithm = self.atom_argument_to_string(4);

                let ints_list = match algorithm.as_str() {
                    "sha3_224" => {
                        let mut context = Sha3_224::new();
                        context.input(&bytes);
                        Addr::HeapCell(
                            self.heap.to_list(
                                context
                                    .result()
                                    .as_ref()
                                    .iter()
                                    .map(|b| HeapCellValue::from(Addr::Fixnum(*b as isize))),
                            ),
                        )
                    }
                    "sha3_256" => {
                        let mut context = Sha3_256::new();
                        context.input(&bytes);
                        Addr::HeapCell(
                            self.heap.to_list(
                                context
                                    .result()
                                    .as_ref()
                                    .iter()
                                    .map(|b| HeapCellValue::from(Addr::Fixnum(*b as isize))),
                            ),
                        )
                    }
                    "sha3_384" => {
                        let mut context = Sha3_384::new();
                        context.input(&bytes);
                        Addr::HeapCell(
                            self.heap.to_list(
                                context
                                    .result()
                                    .as_ref()
                                    .iter()
                                    .map(|b| HeapCellValue::from(Addr::Fixnum(*b as isize))),
                            ),
                        )
                    }
                    "sha3_512" => {
                        let mut context = Sha3_512::new();
                        context.input(&bytes);
                        Addr::HeapCell(
                            self.heap.to_list(
                                context
                                    .result()
                                    .as_ref()
                                    .iter()
                                    .map(|b| HeapCellValue::from(Addr::Fixnum(*b as isize))),
                            ),
                        )
                    }
                    "blake2s256" => {
                        let mut context = Blake2s::new();
                        context.input(&bytes);
                        Addr::HeapCell(
                            self.heap.to_list(
                                context
                                    .result()
                                    .as_ref()
                                    .iter()
                                    .map(|b| HeapCellValue::from(Addr::Fixnum(*b as isize))),
                            ),
                        )
                    }
                    "blake2b512" => {
                        let mut context = Blake2b::new();
                        context.input(&bytes);
                        Addr::HeapCell(
                            self.heap.to_list(
                                context
                                    .result()
                                    .as_ref()
                                    .iter()
                                    .map(|b| HeapCellValue::from(Addr::Fixnum(*b as isize))),
                            ),
                        )
                    }
                    "ripemd160" => {
                        let mut context = Ripemd160::new();
                        context.input(&bytes);
                        Addr::HeapCell(
                            self.heap.to_list(
                                context
                                    .result()
                                    .as_ref()
                                    .iter()
                                    .map(|b| HeapCellValue::from(Addr::Fixnum(*b as isize))),
                            ),
                        )
                    }
                    _ => {
                        let ints = digest::digest(
                            match algorithm.as_str() {
                                "sha256" => &digest::SHA256,
                                "sha384" => &digest::SHA384,
                                "sha512" => &digest::SHA512,
                                "sha512_256" => &digest::SHA512_256,
                                _ => {
                                    unreachable!()
                                }
                            },
                            &bytes,
                        );
                        Addr::HeapCell(
                            self.heap.to_list(
                                ints.as_ref()
                                    .iter()
                                    .map(|b| HeapCellValue::from(Addr::Fixnum(*b as isize))),
                            ),
                        )
                    }
                };

                (self.unify_fn)(self, self[temp_v!(3)], ints_list);
            }
            &SystemClauseType::CryptoDataHKDF => {
                let encoding = self.atom_argument_to_string(2);
                let data = self.string_encoding_bytes(1, &encoding);
                let stub1 = MachineError::functor_stub(clause_name!("crypto_data_hkdf"), 4);
                let salt = self.integers_to_bytevec(temp_v!(3), stub1);
                let stub2 = MachineError::functor_stub(clause_name!("crypto_data_hkdf"), 4);
                let info = self.integers_to_bytevec(temp_v!(4), stub2);

                let algorithm = self.atom_argument_to_string(5);

                let length = self.store(self.deref(self[temp_v!(6)]));

                let length = match Number::try_from((length, &self.heap)) {
                    Ok(Number::Fixnum(n)) => usize::try_from(n).unwrap(),
                    Ok(Number::Integer(n)) => match n.to_usize() {
                        Some(u) => u,
                        _ => {
                            self.fail = true;
                            return Ok(());
                        }
                    },
                    _ => {
                        unreachable!()
                    }
                };

                let ints_list = {
                    let digest_alg = match algorithm.as_str() {
                        "sha256" => hkdf::HKDF_SHA256,
                        "sha384" => hkdf::HKDF_SHA384,
                        "sha512" => hkdf::HKDF_SHA512,
                        _ => {
                            self.fail = true;
                            return Ok(());
                        }
                    };
                    let salt = hkdf::Salt::new(digest_alg, &salt);
                    let mut bytes: Vec<u8> = Vec::new();
                    bytes.resize(length, 0);
                    match salt.extract(&data).expand(&[&info[..]], MyKey(length)) {
                        Ok(r) => {
                            r.fill(&mut bytes).unwrap();
                        }
                        _ => {
                            self.fail = true;
                            return Ok(());
                        }
                    }

                    Addr::HeapCell(
                        self.heap.to_list(
                            bytes
                                .iter()
                                .map(|b| HeapCellValue::from(Addr::Fixnum(*b as isize))),
                        ),
                    )
                };

                (self.unify_fn)(self, self[temp_v!(7)], ints_list);
            }
            &SystemClauseType::CryptoPasswordHash => {
                let stub1 = MachineError::functor_stub(clause_name!("crypto_password_hash"), 3);
                let data = self.integers_to_bytevec(temp_v!(1), stub1);
                let stub2 = MachineError::functor_stub(clause_name!("crypto_password_hash"), 3);
                let salt = self.integers_to_bytevec(temp_v!(2), stub2);

                let iterations = self.store(self.deref(self[temp_v!(3)]));

                let iterations = match Number::try_from((iterations, &self.heap)) {
                    Ok(Number::Fixnum(n)) => u64::try_from(n).unwrap(),
                    Ok(Number::Integer(n)) => match n.to_u64() {
                        Some(i) => i,
                        None => {
                            self.fail = true;
                            return Ok(());
                        }
                    },
                    _ => {
                        unreachable!()
                    }
                };

                let ints_list = {
                    let mut bytes = [0u8; digest::SHA512_OUTPUT_LEN];
                    pbkdf2::derive(
                        pbkdf2::PBKDF2_HMAC_SHA512,
                        NonZeroU32::new(iterations as u32).unwrap(),
                        &salt,
                        &data,
                        &mut bytes,
                    );

                    Addr::HeapCell(
                        self.heap.to_list(
                            bytes
                                .iter()
                                .map(|b| HeapCellValue::from(Addr::Fixnum(*b as isize))),
                        ),
                    )
                };

                (self.unify_fn)(self, self[temp_v!(4)], ints_list);
            }
            &SystemClauseType::CryptoDataEncrypt => {
                let encoding = self.atom_argument_to_string(3);
                let data = self.string_encoding_bytes(1, &encoding);
                let aad = self.string_encoding_bytes(2, &encoding);
                let stub2 = MachineError::functor_stub(clause_name!("crypto_data_encrypt"), 7);
                let key = self.integers_to_bytevec(temp_v!(4), stub2);
                let stub3 = MachineError::functor_stub(clause_name!("crypto_data_encrypt"), 7);
                let iv = self.integers_to_bytevec(temp_v!(5), stub3);

                let unbound_key = aead::UnboundKey::new(&aead::CHACHA20_POLY1305, &key).unwrap();
                let nonce = aead::Nonce::try_assume_unique_for_key(&iv).unwrap();
                let key = aead::LessSafeKey::new(unbound_key);

                let mut in_out = data.clone();
                let tag = match key.seal_in_place_separate_tag(
                    nonce,
                    aead::Aad::from(aad),
                    &mut in_out,
                ) {
                    Ok(d) => d,
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                };

                let tag_list = Addr::HeapCell(
                    self.heap.to_list(
                        tag.as_ref()
                            .iter()
                            .map(|b| HeapCellValue::from(Addr::Fixnum(*b as isize))),
                    ),
                );

                let complete_string = {
                    let buffer = String::from_iter(in_out.iter().map(|b| *b as char));
                    self.heap.put_complete_string(&buffer)
                };

                (self.unify_fn)(self, self[temp_v!(6)], tag_list);
                (self.unify_fn)(self, self[temp_v!(7)], complete_string);
            }
            &SystemClauseType::CryptoDataDecrypt => {
                let data = self.string_encoding_bytes(1, "octet");
                let encoding = self.atom_argument_to_string(5);
                let aad = self.string_encoding_bytes(2, &encoding);
                let stub1 = MachineError::functor_stub(clause_name!("crypto_data_decrypt"), 7);
                let key = self.integers_to_bytevec(temp_v!(3), stub1);
                let stub2 = MachineError::functor_stub(clause_name!("crypto_data_decrypt"), 7);
                let iv = self.integers_to_bytevec(temp_v!(4), stub2);

                let unbound_key = aead::UnboundKey::new(&aead::CHACHA20_POLY1305, &key).unwrap();
                let nonce = aead::Nonce::try_assume_unique_for_key(&iv).unwrap();
                let key = aead::LessSafeKey::new(unbound_key);

                let mut in_out = data.clone();

                let complete_string = {
                    let decrypted_data =
                        match key.open_in_place(nonce, aead::Aad::from(aad), &mut in_out) {
                            Ok(d) => d,
                            _ => {
                                self.fail = true;
                                return Ok(());
                            }
                        };

                    let buffer = match encoding.as_str() {
                        "octet" => String::from_iter(decrypted_data.iter().map(|b| *b as char)),
                        "utf8" => match String::from_utf8(decrypted_data.to_vec()) {
                            Ok(str) => str,
                            _ => {
                                self.fail = true;
                                return Ok(());
                            }
                        },
                        _ => {
                            unreachable!()
                        }
                    };

                    self.heap.put_complete_string(&buffer)
                };

                (self.unify_fn)(self, self[temp_v!(6)], complete_string);
            }
            &SystemClauseType::CryptoCurveScalarMult => {
                let curve = self.atom_argument_to_string(1);
                let curve_id = match curve.as_str() {
                    "secp112r1" => Nid::SECP112R1,
                    "secp256k1" => Nid::SECP256K1,
                    _ => {
                        unreachable!()
                    }
                };

                let scalar = self.store(self.deref(self[temp_v!(2)]));

                let scalar = match Number::try_from((scalar, &self.heap)) {
                    Ok(Number::Fixnum(n)) => Integer::from(n),
                    Ok(Number::Integer(n)) => Integer::from(&*n.clone()),
                    _ => {
                        unreachable!()
                    }
                };

                let stub = MachineError::functor_stub(clause_name!("crypto_curve_scalar_mult"), 5);
                let qbytes = self.integers_to_bytevec(temp_v!(3), stub);

                let mut bnctx = BigNumContext::new().unwrap();
                let group = EcGroup::from_curve_name(curve_id).unwrap();
                let mut point = EcPoint::from_bytes(&group, &qbytes, &mut bnctx).unwrap();
                let scalar_bn = BigNum::from_dec_str(&scalar.to_string()).unwrap();
                let mut result = EcPoint::new(&group).unwrap();
                result.mul(&group, &mut point, &scalar_bn, &mut bnctx).ok();

                let mut rx = BigNum::new().unwrap();
                let mut ry = BigNum::new().unwrap();
                result
                    .affine_coordinates_gfp(&group, &mut rx, &mut ry, &mut bnctx)
                    .ok();
                let sx = self
                    .heap
                    .put_complete_string(&rx.to_dec_str().unwrap().to_string());
                let sy = self
                    .heap
                    .put_complete_string(&ry.to_dec_str().unwrap().to_string());

                (self.unify_fn)(self, self[temp_v!(4)], sx);
                (self.unify_fn)(self, self[temp_v!(5)], sy);
            }
            &SystemClauseType::Ed25519NewKeyPair => {
                let pkcs8_bytes = signature::Ed25519KeyPair::generate_pkcs8(rng()).unwrap();
                let complete_string = {
                    let buffer = String::from_iter(pkcs8_bytes.as_ref().iter().map(|b| *b as char));
                    self.heap.put_complete_string(&buffer)
                };

                (self.unify_fn)(self, self[temp_v!(1)], complete_string);
            }
            &SystemClauseType::Ed25519KeyPairPublicKey => {
                let bytes = self.string_encoding_bytes(1, "octet");

                let key_pair = match signature::Ed25519KeyPair::from_pkcs8(&bytes) {
                    Ok(kp) => kp,
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                };

                let complete_string = {
                    let buffer = String::from_iter(
                        key_pair.public_key().as_ref().iter().map(|b| *b as char),
                    );
                    self.heap.put_complete_string(&buffer)
                };

                (self.unify_fn)(self, self[temp_v!(2)], complete_string);
            }
            &SystemClauseType::Ed25519Sign => {
                let key = self.string_encoding_bytes(1, "octet");
                let encoding = self.atom_argument_to_string(3);
                let data = self.string_encoding_bytes(2, &encoding);

                let key_pair = match signature::Ed25519KeyPair::from_pkcs8(&key) {
                    Ok(kp) => kp,
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                };

                let sig = key_pair.sign(&data);

                let sig_list = Addr::HeapCell(
                    self.heap.to_list(
                        sig.as_ref()
                            .iter()
                            .map(|b| HeapCellValue::from(Addr::Fixnum(*b as isize))),
                    ),
                );

                (self.unify_fn)(self, self[temp_v!(4)], sig_list);
            }
            &SystemClauseType::Ed25519Verify => {
                let key = self.string_encoding_bytes(1, "octet");
                let encoding = self.atom_argument_to_string(3);
                let data = self.string_encoding_bytes(2, &encoding);
                let stub = MachineError::functor_stub(clause_name!("ed25519_verify"), 5);
                let signature = self.integers_to_bytevec(temp_v!(4), stub);

                let peer_public_key = signature::UnparsedPublicKey::new(&signature::ED25519, &key);
                match peer_public_key.verify(&data, &signature) {
                    Ok(_) => {}
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                }
            }
            &SystemClauseType::Curve25519ScalarMult => {
                let stub1 = MachineError::functor_stub(clause_name!("curve25519_scalar_mult"), 3);
                let scalar_bytes = self.integers_to_bytevec(temp_v!(1), stub1);
                let scalar = Scalar(<[u8; 32]>::try_from(&scalar_bytes[..]).unwrap());

                let stub2 = MachineError::functor_stub(clause_name!("curve25519_scalar_mult"), 3);
                let point_bytes = self.integers_to_bytevec(temp_v!(2), stub2);
                let point = GroupElement(<[u8; 32]>::try_from(&point_bytes[..]).unwrap());

                let result = scalarmult(&scalar, &point).unwrap();

                let string = String::from_iter(result[..].iter().map(|b| *b as char));
                let cstr = self.heap.put_complete_string(&string);
                (self.unify_fn)(self, self[temp_v!(3)], cstr);
            }
            &SystemClauseType::LoadHTML => {
                let string = self.heap_pstr_iter(self[temp_v!(1)]).to_string();
                let doc = select::document::Document::from_read(string.as_bytes()).unwrap();
                let result = self.html_node_to_term(indices, doc.nth(0).unwrap());

                (self.unify_fn)(self, self[temp_v!(2)], result);
            }
            &SystemClauseType::LoadXML => {
                let string = self.heap_pstr_iter(self[temp_v!(1)]).to_string();
                match roxmltree::Document::parse(&string) {
                    Ok(doc) => {
                        let result = self.xml_node_to_term(indices, doc.root_element());
                        (self.unify_fn)(self, self[temp_v!(2)], result);
                    }
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                }
            }
            &SystemClauseType::GetEnv => {
                let key = self.heap_pstr_iter(self[temp_v!(1)]).to_string();
                match env::var(key) {
                    Ok(value) => {
                        let cstr = self.heap.put_complete_string(&value);
                        (self.unify_fn)(self, self[temp_v!(2)], cstr);
                    }
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                }
            }
            &SystemClauseType::SetEnv => {
                let key = self.heap_pstr_iter(self[temp_v!(1)]).to_string();
                let value = self.heap_pstr_iter(self[temp_v!(2)]).to_string();
                env::set_var(key, value);
            }
            &SystemClauseType::UnsetEnv => {
                let key = self.heap_pstr_iter(self[temp_v!(1)]).to_string();
                env::remove_var(key);
            }
            &SystemClauseType::PID => {
                let a1 = self[temp_v!(1)];
                let pid = process::id();
                let addr = self.heap.put_constant(Constant::Integer(Rc::new(Integer::from(pid))));
                (self.unify_fn)(self, a1, addr);
            }
            &SystemClauseType::CharsBase64 => {
                let padding = self.atom_argument_to_string(3);
                let charset = self.atom_argument_to_string(4);

                let config = if padding == "true" {
                    if charset == "standard" {
                        base64::STANDARD
                    } else {
                        base64::URL_SAFE
                    }
                } else {
                    if charset == "standard" {
                        base64::STANDARD_NO_PAD
                    } else {
                        base64::URL_SAFE_NO_PAD
                    }
                };

                if self.store(self.deref(self[temp_v!(1)])).is_ref() {
                    let b64 = self.heap_pstr_iter(self[temp_v!(2)]).to_string();
                    let bytes = base64::decode_config(b64, config);

                    match bytes {
                        Ok(bs) => {
                            let string = String::from_iter(bs.iter().map(|b| *b as char));
                            let cstr = self.heap.put_complete_string(&string);
                            (self.unify_fn)(self, self[temp_v!(1)], cstr);
                        }
                        _ => {
                            self.fail = true;
                            return Ok(());
                        }
                    }
                } else {
                    let mut bytes = vec![];
                    for c in self.heap_pstr_iter(self[temp_v!(1)]).to_string().chars() {
                        if c as u32 > 255 {
                            let stub = MachineError::functor_stub(clause_name!("chars_base64"), 3);

                            let err = MachineError::type_error(
                                self.heap.h(),
                                ValidType::Byte,
                                Addr::Char(c),
                            );

                            return Err(self.error_form(err, stub));
                        }

                        bytes.push(c as u8);
                    }
                    let b64 = base64::encode_config(bytes, config);

                    let cstr = self.heap.put_complete_string(&b64);
                    (self.unify_fn)(self, self[temp_v!(2)], cstr);
                }
            }
            &SystemClauseType::LoadLibraryAsStream => {
                let library_name = atom_from!(self, self.store(self.deref(self[temp_v!(1)])));

                use crate::LIBRARIES;

                match LIBRARIES.borrow().get(library_name.as_str()) {
                    Some(library) => {
                        let var_ref = Ref::HeapCell(
                            self.heap
                                .push(HeapCellValue::Stream(Stream::from(*library))),
                        );

                        self.bind(var_ref, self[temp_v!(2)]);

                        let mut path_buf = machine::current_dir();

                        path_buf.push("/lib");
                        path_buf.push(library_name.as_str());

                        let library_path_str = path_buf.to_str().unwrap();
                        let library_path =
                            clause_name!(library_path_str.to_string(), self.atom_tbl);

                        let library_path_ref =
                            Ref::HeapCell(self.heap.push(HeapCellValue::Atom(library_path, None)));

                        self.bind(library_path_ref, self[temp_v!(3)]);
                    }
                    None => {
                        return Err(self.error_form(
                            MachineError::existence_error(
                                self.heap.h(),
                                ExistenceError::ModuleSource(ModuleSource::Library(library_name)),
                            ),
                            MachineError::functor_stub(clause_name!("load"), 1),
                        ));
                    }
                }
            }
            &SystemClauseType::DevourWhitespace => {
                let stream = self.get_stream_or_alias(
                    self[temp_v!(1)],
                    &indices.stream_aliases,
                    "$devour_whitespace",
                    1,
                )?;

                match self.devour_whitespace(stream, self.atom_tbl.clone()) {
                    Ok(false) => {} // not at EOF.
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                }
            }
            &SystemClauseType::IsSTOEnabled => {
                if self.unify_fn as usize == MachineState::unify_with_occurs_check as usize {
                    let value = self
                        .heap
                        .to_unifiable(HeapCellValue::Atom(clause_name!("true"), None));

                    (self.unify_fn)(self, self[temp_v!(1)], value);
                } else if self.unify_fn as usize
                    == MachineState::unify_with_occurs_check_with_error as usize
                {
                    let value = self
                        .heap
                        .to_unifiable(HeapCellValue::Atom(clause_name!("error"), None));

                    (self.unify_fn)(self, self[temp_v!(1)], value);
                } else {
                    let value = self
                        .heap
                        .to_unifiable(HeapCellValue::Atom(clause_name!("false"), None));

                    (self.unify_fn)(self, self[temp_v!(1)], value);
                }
            }
            &SystemClauseType::SetSTOAsUnify => {
                self.unify_fn = MachineState::unify_with_occurs_check;
                self.bind_fn = MachineState::bind_with_occurs_check_wrapper;
            }
            &SystemClauseType::SetNSTOAsUnify => {
                self.unify_fn = MachineState::unify;
                self.bind_fn = MachineState::bind;
            }
            &SystemClauseType::SetSTOWithErrorAsUnify => {
                self.unify_fn = MachineState::unify_with_occurs_check_with_error;
                self.bind_fn = MachineState::bind_with_occurs_check_with_error_wrapper;
            }
            &SystemClauseType::HomeDirectory => {
                let path = match dirs_next::home_dir() {
                    Some(path) => path,
                    None => {
                        self.fail = true;
                        return Ok(());
                    }
                };

                if path.is_dir() {
                    if let Some(path) = path.to_str() {
                        let path_string = self.heap.put_complete_string(path);

                        self.unify(self[temp_v!(1)], path_string);
                        return return_from_clause!(self.last_call, self);
                    }
                }

                self.fail = true;
            }
            &SystemClauseType::DebugHook => {
                self.fail = false;
            }
            &SystemClauseType::PopCount => {
                let number  = self.store(self.deref(self[temp_v!(1)]));
                let count = match Number::try_from((number, &self.heap)) {
                    Ok(Number::Fixnum(n)) => Integer::from(n.count_ones()),
                    Ok(Number::Integer(n)) => Integer::from((&*n).count_ones().unwrap()),
                    _ => {
                        unreachable!()
                    }
                };

                let pop_count = self.heap.to_unifiable(HeapCellValue::Integer(Rc::new(count)));
                (self.unify_fn)(self, self[temp_v!(2)], pop_count);
            }
        };

        return_from_clause!(self.last_call, self)
    }

    pub(super) fn systemtime_to_timestamp(&mut self, system_time: SystemTime) -> Addr {
        let datetime: DateTime<Local> = system_time.into();

        let mut fstr = "[".to_string();
        let specifiers = vec![
            "Y", "m", "d", "H", "M", "S", "y", "b", "B", "a", "A", "w", "u", "U", "W", "j", "D",
            "x", "v",
        ];
        for spec in specifiers {
            fstr.push_str(&format!("'{}'=\"%{}\", ", spec, spec).to_string());
        }
        fstr.push_str("finis].");
        let s = datetime.format(&fstr).to_string();
        self.heap.put_complete_string(&s)
    }

    pub(super) fn atom_argument_to_string(&mut self, atom_arg: usize) -> String {
        match self.store(self.deref(self[temp_v!(atom_arg)])) {
            Addr::Con(h) if self.heap.atom_at(h) => {
                if let HeapCellValue::Atom(ref atom, _) = &self.heap[h] {
                    atom.as_str().to_string()
                } else {
                    unreachable!()
                }
            }
            _ => {
                unreachable!()
            }
        }
    }

    pub(super) fn string_encoding_bytes(&mut self, data_arg: usize, encoding: &str) -> Vec<u8> {
        let data = self.heap_pstr_iter(self[temp_v!(data_arg)]).to_string();

        match encoding {
            "utf8" => data.into_bytes(),
            "octet" => {
                let mut buf = vec![];
                for c in data.chars() {
                    buf.push(c as u8);
                }
                buf
            }
            _ => {
                unreachable!()
            }
        }
    }

    pub(super) fn xml_node_to_term(
        &mut self,
        indices: &mut IndexStore,
        node: roxmltree::Node,
    ) -> Addr {
        if node.is_text() {
            let string = String::from(node.text().unwrap());
            self.heap.put_complete_string(&string)
        } else {
            let mut avec = Vec::new();
            for attr in node.attributes() {
                let chars = clause_name!(String::from(attr.name()), self.atom_tbl);
                let name = self.heap.to_unifiable(HeapCellValue::Atom(chars, None));

                let value = self.heap.put_complete_string(&attr.value());

                avec.push(HeapCellValue::Addr(Addr::HeapCell(self.heap.h())));

                self.heap
                    .push(HeapCellValue::NamedStr(2, clause_name!("="), None));
                self.heap.push(HeapCellValue::Addr(name));
                self.heap.push(HeapCellValue::Addr(value));
            }
            let attrs = Addr::HeapCell(self.heap.to_list(avec.into_iter()));

            let mut cvec = Vec::new();
            for child in node.children() {
                cvec.push(self.xml_node_to_term(indices, child));
            }
            let children = Addr::HeapCell(self.heap.to_list(cvec.into_iter()));

            let chars = clause_name!(String::from(node.tag_name().name()), self.atom_tbl);
            let tag = self.heap.to_unifiable(HeapCellValue::Atom(chars, None));

            let result = Addr::HeapCell(self.heap.h());

            self.heap
                .push(HeapCellValue::NamedStr(3, clause_name!("element"), None));
            self.heap.push(HeapCellValue::Addr(tag));
            self.heap.push(HeapCellValue::Addr(attrs));
            self.heap.push(HeapCellValue::Addr(children));

            result
        }
    }

    pub(super) fn html_node_to_term(
        &mut self,
        indices: &mut IndexStore,
        node: select::node::Node,
    ) -> Addr {
        match node.name() {
            None => {
                let string = String::from(node.text());
                self.heap.put_complete_string(&string)
            }
            Some(name) => {
                let mut avec = Vec::new();
                for attr in node.attrs() {
                    let chars = clause_name!(String::from(attr.0), self.atom_tbl);
                    let name = self.heap.to_unifiable(HeapCellValue::Atom(chars, None));

                    let value = self.heap.put_complete_string(&String::from(attr.1));

                    avec.push(HeapCellValue::Addr(Addr::HeapCell(self.heap.h())));

                    self.heap
                        .push(HeapCellValue::NamedStr(2, clause_name!("="), None));
                    self.heap.push(HeapCellValue::Addr(name));
                    self.heap.push(HeapCellValue::Addr(value));
                }
                let attrs = Addr::HeapCell(self.heap.to_list(avec.into_iter()));

                let mut cvec = Vec::new();
                for child in node.children() {
                    cvec.push(self.html_node_to_term(indices, child));
                }
                let children = Addr::HeapCell(self.heap.to_list(cvec.into_iter()));

                let chars = clause_name!(String::from(name), self.atom_tbl);
                let tag = self.heap.to_unifiable(HeapCellValue::Atom(chars, None));

                let result = Addr::HeapCell(self.heap.h());

                self.heap
                    .push(HeapCellValue::NamedStr(3, clause_name!("element"), None));
                self.heap.push(HeapCellValue::Addr(tag));
                self.heap.push(HeapCellValue::Addr(attrs));
                self.heap.push(HeapCellValue::Addr(children));

                result
            }
        }
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
