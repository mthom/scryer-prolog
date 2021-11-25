use crate::parser::ast::*;
use crate::parser::parser::*;

use lazy_static::lazy_static;

use crate::arena::*;
use crate::atom_table::*;
use crate::clause_types::*;
use crate::forms::*;
use crate::heap_iter::*;
use crate::heap_print::*;
use crate::instructions::*;
use crate::machine;
use crate::machine::code_repo::CodeRepo;
use crate::machine::code_walker::*;
use crate::machine::copier::*;
use crate::machine::heap::*;
use crate::machine::machine_errors::*;
use crate::machine::machine_indices::*;
use crate::machine::machine_state::*;
use crate::machine::partial_string::*;
use crate::machine::preprocessor::to_op_decl;
use crate::machine::stack::*;
use crate::machine::streams::*;
use crate::parser::char_reader::*;
use crate::parser::rug::Integer;
use crate::read::*;
use crate::types::*;

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

use native_tls::{TlsConnector,TlsAcceptor,Identity};

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

#[derive(Debug, Clone, Copy)]
pub struct BrentAlgState {
    pub hare: usize,
    pub tortoise: usize,
    pub power: usize,
    pub lam: usize,
    pub pstr_chars: usize,
}

impl BrentAlgState {
    pub fn new(hare: usize) -> Self {
        Self {
            hare,
            tortoise: hare,
            power: 1,
            lam: 0,
            pstr_chars: 0,
        }
    }

    #[inline(always)]
    pub fn teleport_tortoise(&mut self) {
        if self.lam == self.power {
            self.tortoise = self.hare;
            self.power <<= 1;
            self.lam = 0;
        }
    }

    #[inline(always)]
    pub fn step(&mut self, hare: usize) -> Option<CycleSearchResult> {
        self.hare = hare;
        self.lam += 1;

        if self.tortoise == self.hare {
            return Some(CycleSearchResult::NotList);
        } else {
            self.teleport_tortoise();
        }

        None
    }

    #[inline(always)]
    pub fn num_steps(&self) -> usize {
        return self.lam + self.pstr_chars + self.power - 1;
    }

    pub fn to_result(mut self, heap: &[HeapCellValue]) -> CycleSearchResult {
        if let Some(var) = heap[self.hare].as_var() {
            return CycleSearchResult::PartialList(self.num_steps(), var);
        }

        read_heap_cell!(heap[self.hare],
            (HeapCellValueTag::PStrOffset) => {
                let n = cell_as_fixnum!(heap[self.hare+1]).get_num() as usize;

                let pstr = cell_as_string!(heap[self.hare]);
                self.pstr_chars += pstr.as_str_from(n).chars().count();

                CycleSearchResult::PStrLocation(self.num_steps(), n)
            }
            (HeapCellValueTag::Atom, (name, arity)) => {
                if name == atom!("[]") && arity == 0 {
                    CycleSearchResult::ProperList(self.num_steps())
                } else {
                    CycleSearchResult::NotList
                }
            }
            _ => {
                CycleSearchResult::NotList
            }
        )
    }

    fn add_pstr_chars_and_step(&mut self, heap: &[HeapCellValue], h: usize) -> Option<CycleSearchResult> {
        read_heap_cell!(heap[h],
            (HeapCellValueTag::CStr, cstr_atom) => {
                let cstr = PartialString::from(cstr_atom);

                self.pstr_chars += cstr.as_str_from(0).chars().count();
                Some(CycleSearchResult::ProperList(self.num_steps()))
            }
            (HeapCellValueTag::PStr, pstr_atom) => {
                let pstr = PartialString::from(pstr_atom);

                self.pstr_chars += pstr.as_str_from(0).chars().count() - 1;
                self.step(h+1)
            }
            (HeapCellValueTag::PStrOffset, offset) => {
                let pstr = cell_as_string!(heap[offset]);
                let n = cell_as_fixnum!(heap[h+1]).get_num() as usize;

                self.pstr_chars += pstr.as_str_from(n).chars().count();

                if let HeapCellValueTag::PStr = heap[offset].get_tag() {
                    self.pstr_chars -= 1;
                    self.step(offset+1)
                } else {
                    debug_assert!(heap[offset].get_tag() == HeapCellValueTag::CStr);
                    Some(CycleSearchResult::ProperList(self.num_steps()))
                }
            }
            _ => {
                unreachable!()
            }
        )
    }
}

impl MachineState {
    #[inline(always)]
    pub fn brents_alg_step(&self, brent_st: &mut BrentAlgState) -> Option<CycleSearchResult> {
        let deref_v = self.deref(self.heap[brent_st.hare]);
        let store_v = self.store(deref_v);

        if let Some(var) = store_v.as_var() {
            return Some(CycleSearchResult::PartialList(brent_st.num_steps(), var));
        }

        if store_v == empty_list_as_cell!() {
            return Some(CycleSearchResult::ProperList(brent_st.num_steps()));
        }

        read_heap_cell!(store_v,
            (HeapCellValueTag::PStrLoc, h) => {
                brent_st.add_pstr_chars_and_step(&self.heap, h)
            }
            (HeapCellValueTag::PStrOffset) => {
                brent_st.add_pstr_chars_and_step(&self.heap, brent_st.hare)
            }
            (HeapCellValueTag::CStr, cstr_atom) => {
                let cstr = PartialString::from(cstr_atom);

                brent_st.pstr_chars += cstr.as_str_from(0).chars().count();
                Some(CycleSearchResult::ProperList(brent_st.num_steps()))
            }
            (HeapCellValueTag::Lis, h) => {
                brent_st.step(h+1)
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.heap[s]).get_name_and_arity();

                if name == atom!(".") && arity == 2 {
                    brent_st.step(s+2)
                } else {
                    Some(CycleSearchResult::NotList)
                }
            }
            (HeapCellValueTag::Atom, (_name, arity)) => {
                debug_assert!(arity == 0);
                Some(CycleSearchResult::NotList)
            }
            _ => {
                Some(CycleSearchResult::NotList)
            }
        )
    }

    pub fn detect_cycles(&self, value: HeapCellValue) -> CycleSearchResult {
        let deref_v = self.deref(value);
        let store_v = self.store(deref_v);

        let mut pstr_chars = 0;

        let hare = read_heap_cell!(store_v,
            (HeapCellValueTag::Lis, offset) => {
                offset+1
            }
            (HeapCellValueTag::PStrLoc, h) => {
                let (h_offset, n) = pstr_loc_and_offset(&self.heap, h);
                let n = n.get_num() as usize;
                let pstr = cell_as_string!(self.heap[h_offset]);

                pstr_chars = pstr.as_str_from(n).chars().count() - 1;

                if self.heap[h].get_tag() == HeapCellValueTag::PStrOffset {
                    debug_assert!(self.heap[h].get_tag() == HeapCellValueTag::PStrOffset);

                    if self.heap[h_offset].get_tag() == HeapCellValueTag::CStr {
                        return CycleSearchResult::ProperList(pstr_chars + 1);
                    }
                }

                h_offset+1
            }
            (HeapCellValueTag::PStrOffset) => {
                unreachable!()
            }
            (HeapCellValueTag::CStr, cstr_atom) => {
                let cstr = PartialString::from(cstr_atom);
                return CycleSearchResult::ProperList(cstr.as_str_from(0).chars().count());
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.heap[s])
                    .get_name_and_arity();

                if name == atom!("[]") && arity == 0 {
                    return CycleSearchResult::EmptyList;
                } else if name == atom!(".") && arity == 2 {
                    s + 2
                } else {
                    return CycleSearchResult::NotList;
                }
            }
            (HeapCellValueTag::Atom, (name, arity)) => {
                if name == atom!("[]") && arity == 0 {
                    return CycleSearchResult::EmptyList;
                } else {
                    return CycleSearchResult::NotList;
                }
            }
            _ => {
                return CycleSearchResult::NotList;
            }
        );

        let mut brent_st = BrentAlgState::new(hare);

        brent_st.power += 1; // advance a step.
        brent_st.pstr_chars = pstr_chars;

        loop {
            if let Some(result) = self.brents_alg_step(&mut brent_st) {
                return result;
            }
        }
    }

    pub fn detect_cycles_with_max(&self, max_steps: usize, value: HeapCellValue) -> CycleSearchResult {
        let deref_v = self.deref(value);
        let store_v = self.store(deref_v);

        // let mut pstr_chars = 0;

        let hare = read_heap_cell!(store_v,
            (HeapCellValueTag::Lis, offset) => {
                if max_steps > 0 {
                    offset+1
                } else {
                    return CycleSearchResult::UntouchedList(offset);
                }
            }
            (HeapCellValueTag::PStrLoc, h) => {
                let (h_offset, _n) = pstr_loc_and_offset(&self.heap, h);

                if self.heap[h].get_tag() == HeapCellValueTag::PStr {
                    h_offset+1
                } else {
                    debug_assert!(self.heap[h].get_tag() == HeapCellValueTag::PStrOffset);
                    h
                }
            }
            (HeapCellValueTag::PStrOffset) => {
                unreachable!()
            }
            (HeapCellValueTag::CStr, cstr_atom) => {
                return if max_steps > 0 {
                    let cstr = PartialString::from(cstr_atom);
                    let pstr_chars = cstr.as_str_from(0).chars().count();

                    if pstr_chars < max_steps {
                        CycleSearchResult::ProperList(pstr_chars)
                    } else {
                        CycleSearchResult::UntouchedCStr(cstr_atom, max_steps)
                    }
                } else {
                    CycleSearchResult::UntouchedCStr(cstr_atom, 0)
                };
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.heap[s]).get_name_and_arity();

                if name == atom!("[]") && arity == 0 {
                    return CycleSearchResult::EmptyList;
                } else if name == atom!(".") && arity == 2 {
                    if max_steps > 0 {
                        s + 2
                    } else {
                        return CycleSearchResult::UntouchedList(s + 1);
                    }
                } else {
                    return CycleSearchResult::NotList;
                }
            }
            (HeapCellValueTag::Atom, (name, arity)) => {
                if name == atom!("[]") && arity == 0 {
                    return CycleSearchResult::EmptyList;
                } else {
                    return CycleSearchResult::NotList;
                }
            }
            _ => {
                return CycleSearchResult::NotList;
            }
        );

        let mut brent_st = BrentAlgState::new(hare);

        brent_st.power += 1; // advance a step.
        // brent_st.pstr_chars = pstr_chars;

        loop {
            if brent_st.num_steps() == max_steps {
                return brent_st.to_result(&self.heap);
            }

            if let Some(result) = self.brents_alg_step(&mut brent_st) {
                return result;
            }
        }
    }

    fn term_variables_under_max_depth(
	    &mut self,
	    term: HeapCellValue,
	    max_depth: usize,
	    list_of_vars: HeapCellValue,
    ) {
	    let mut seen_set = IndexSet::new();

	    {
	        let mut iter = stackful_post_order_iter(&mut self.heap, term);

            while let Some(value) = iter.next() {
		        if iter.parent_stack_len() >= max_depth {
		            iter.pop_stack();
		            continue;
		        }

		        let value = unmark_cell_bits!(value);

		        if value.is_var() && !seen_set.contains(&value) {
		            seen_set.insert(value);
		        }
            }
	    }

        let outcome = heap_loc_as_cell!(
            iter_to_heap_list(
                &mut self.heap,
                seen_set.into_iter().rev(),
            )
        );

        unify_fn!(self, list_of_vars, outcome);
    }

    fn finalize_skip_max_list(&mut self, n: usize, value: HeapCellValue) {
        let target_n = self.registers[1];
        self.unify_fixnum(Fixnum::build_with(n as i64), target_n);

        if !self.fail {
            let xs = self.registers[4];
            unify!(self, value, xs);
        }
    }

    fn skip_max_list_result(&mut self, max_steps: Option<i64>) {
        let search_result = if let Some(max_steps) = max_steps {
            if max_steps == -1 {
                self.detect_cycles(self.registers[3])
            } else {
                self.detect_cycles_with_max(max_steps as usize, self.registers[3])
            }
        } else {
            self.detect_cycles(self.registers[3])
        };

        match search_result {
            CycleSearchResult::PStrLocation(steps, pstr_loc) => {
                self.finalize_skip_max_list(steps, heap_loc_as_cell!(pstr_loc));
            }
            CycleSearchResult::UntouchedList(l) => {
                self.finalize_skip_max_list(0, list_loc_as_cell!(l));
            }
            CycleSearchResult::UntouchedCStr(cstr_atom, n) => {
                self.finalize_skip_max_list(n, string_as_cstr_cell!(cstr_atom));
            }
            CycleSearchResult::EmptyList => {
                self.finalize_skip_max_list(0, empty_list_as_cell!());
            }
            CycleSearchResult::PartialList(n, r) => {
                self.finalize_skip_max_list(n, r.as_heap_cell_value());
            }
            CycleSearchResult::ProperList(steps) => {
                self.finalize_skip_max_list(steps, empty_list_as_cell!())
            }
            CycleSearchResult::NotList => {
                let xs0 = self.registers[3];
                self.finalize_skip_max_list(0, xs0);
            }
        };
    }

    pub fn skip_max_list(&mut self) -> CallResult {
        let max_steps = self.store(self.deref(self.registers[2]));

        if max_steps.is_var() {
            let stub = functor_stub(atom!("$skip_max_list"), 4);
            let err = self.instantiation_error();

            return Err(self.error_form(err, stub));
        }

        let max_steps_n = match Number::try_from(max_steps) {
            Ok(Number::Fixnum(n)) => Some(n.get_num()),
            Ok(Number::Integer(n)) => n.to_i64(),
            _ => None,
        };

        if max_steps_n.map(|i| i >= -1).unwrap_or(false) {
            let n = self.store(self.deref(self.registers[1]));

            match Number::try_from(n) {
                Ok(Number::Integer(n)) => {
                    if &*n == &0 {
                        let xs0 = self.registers[3];
                        let xs = self.registers[4];

                        unify!(self, xs0, xs);
                    } else {
                        self.skip_max_list_result(max_steps_n);
                    }
                }
                Ok(Number::Fixnum(n)) => {
                    if n.get_num() == 0 {
                        let xs0 = self.registers[3];
                        let xs = self.registers[4];

                        unify!(self, xs0, xs);
                    } else {
                        self.skip_max_list_result(max_steps_n);
                    }
                }
                _ => {
                    self.skip_max_list_result(max_steps_n);
                }
            }
        } else {
            let stub = functor_stub(atom!("$skip_max_list"), 4);
            let err = self.type_error(ValidType::Integer, max_steps);

            return Err(self.error_form(err, stub));
        }

        Ok(())
    }
}

impl MachineState {
    #[inline]
    fn install_new_block(&mut self, value: HeapCellValue) -> usize {
        self.block = self.b;
        self.unify_fixnum(Fixnum::build_with(self.block as i64), value);

        self.block
    }

    fn copy_findall_solution(&mut self, lh_offset: usize, copy_target: HeapCellValue) -> usize {
        let threshold = self.lifted_heap.len() - lh_offset;

        let mut copy_ball_term =
            CopyBallTerm::new(&mut self.stack, &mut self.heap, &mut self.lifted_heap);

        copy_ball_term.push(list_loc_as_cell!(threshold + 1));
        copy_ball_term.push(heap_loc_as_cell!(threshold + 3));
        copy_ball_term.push(heap_loc_as_cell!(threshold + 2));

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

    #[inline(always)]
    fn truncate_if_no_lifted_heap_diff(
        &mut self,
        addr_constr: impl Fn(usize) -> HeapCellValue,
    ) {
        read_heap_cell!(self.store(self.deref(self.registers[1])),
            (HeapCellValueTag::Fixnum, n) => {
                let lh_offset = n.get_num() as usize;

                if lh_offset >= self.lifted_heap.len() {
                    self.lifted_heap.truncate(lh_offset);
                } else {
                    let threshold = self.lifted_heap.len() - lh_offset;
                    self.lifted_heap.push(addr_constr(threshold));
                }
            }
            _ => {
                self.fail = true;
            }
        );
    }

    fn get_next_db_ref(&self, indices: &IndexStore, db_ref: &DBRef) -> Option<DBRef> {
        match db_ref {
            DBRef::NamedPred(name, arity) => {
                let key = (*name, *arity);

                if let Some((last_idx, _, _)) = indices.code_dir.get_full(&key) {
                    for idx in last_idx + 1 .. indices.code_dir.len() {
                        let ((name, arity), idx) = indices.code_dir.get_index(idx).unwrap();

                        if idx.is_undefined() {
                            return None;
                        }

                        if SystemClauseType::from(*name, *arity).is_some() {
                            continue;
                        }

                        return Some(DBRef::NamedPred(*name, *arity));
                    }
                }
            }
            DBRef::Op(name, fixity, op_dir) => {
                let key = (*name, *fixity);

                if let Some((last_idx, _, _)) = op_dir.get_full(&key) {
                    if let Some(((name, fixity), _)) = op_dir.get_index(last_idx+1) {
                        return Some(DBRef::Op(*name, *fixity, *op_dir));
                    }
                }
            }
        }

        None
    }

    fn parse_number_from_string(
        &mut self,
        mut string: String,
        indices: &IndexStore,
        stub_gen: impl Fn() -> FunctorStub,
    ) -> CallResult {
        let nx = self.registers[2];

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
                let err = self.syntax_error(err);

                return Err(self.error_form(err, stub_gen()));
            }
        }

        string.push('.');

        let stream = CharReader::new(std::io::Cursor::new(string));
        let mut parser = Parser::new(stream, self);

        match parser.read_term(&CompositeOpDir::new(&indices.op_dir, None)) {
            Err(err) => {
                let err = self.syntax_error(err);
                return Err(self.error_form(err, stub_gen()));
            }
            Ok(Term::Literal(_, Literal::Rational(n))) => {
                self.unify_rational(n, nx);
            }
            Ok(Term::Literal(_, Literal::Float(n))) => {
                self.unify_f64(n, nx);
            }
            Ok(Term::Literal(_, Literal::Integer(n))) => {
                self.unify_big_int(n, nx);
            }
            Ok(Term::Literal(_, Literal::Fixnum(n))) => {
                self.unify_fixnum(n, nx);
            }
            _ => {
                let err = ParserError::ParseBigInt(0, 0);
                let err = self.syntax_error(err);

                return Err(self.error_form(err, stub_gen()));
            }
        }

        Ok(())
    }

    fn call_continuation_chunk(&mut self, chunk: HeapCellValue, return_p: LocalCodePtr) -> LocalCodePtr {
        let chunk = self.store(self.deref(chunk));

        let s = chunk.get_value();
        let arity = cell_as_atom_cell!(self.heap[s]).get_arity();

        let num_cells = arity - 1;
        let p_functor = self.heap[s + 1];

        let cp = to_local_code_ptr(&self.heap, p_functor).unwrap();
        let prev_e = self.e;

        let e = self.stack.allocate_and_frame(num_cells);
        let and_frame = self.stack.index_and_frame_mut(e);

        and_frame.prelude.e = prev_e;
        and_frame.prelude.cp = return_p;

        self.p = CodePtr::Local(cp + 1);

        // adjust cut point to occur after call_continuation.
        if num_cells > 0 {
            if let HeapCellValueTag::Fixnum = self.heap[s + 2].get_tag() {
                and_frame[1] = fixnum_as_cell!(Fixnum::build_with(self.b as i64));
            } else {
                and_frame[1] = self.heap[s + 2];
            }
        }

        for index in s + 3..s + 2 + num_cells {
            and_frame[index - (s + 1)] = self.heap[index];
        }

        self.e = e;
        self.p.local()
    }

    pub fn value_to_str_like(&mut self, value: HeapCellValue) -> Option<AtomOrString> {
        read_heap_cell!(value,
            (HeapCellValueTag::CStr, cstr_atom) => {
                // avoid allocating a String if possible ...
                Some(AtomOrString::Atom(cstr_atom))
            }
            (HeapCellValueTag::Atom, (atom, arity)) => {
                if arity == 0 {
                    // ... likewise.
                    Some(AtomOrString::Atom(atom))
                } else {
                    None
                }
            }
            _ => {
                if value.is_constant() {
                    return None;
                }

                let h = self.heap.len();
                self.heap.push(value);

                let mut iter = HeapPStrIter::new(&self.heap, h);
                let string = iter.to_string();
                let at_terminator = iter.at_string_terminator();

                self.heap.pop();

                // if the iteration doesn't terminate like a string
                // (i.e. with the [] atom or a CStr), it is not
                // "str_like" so return None.
                if at_terminator {
                    Some(AtomOrString::String(string))
                } else {
                    None
                }
            }
        )
    }

    fn codes_to_string(
        &mut self,
        addrs: impl Iterator<Item = HeapCellValue>,
        stub_gen: impl Fn() -> FunctorStub,
    ) -> Result<String, MachineStub> {
        let mut string = String::new();

        for addr in addrs {
            match Number::try_from(addr) {
                Ok(Number::Fixnum(n)) => {
                    match u32::try_from(n.get_num()) {
                        Ok(n) => {
                            if let Some(c) = std::char::from_u32(n) {
                                string.push(c);
                                continue;
                            }
                        }
                        _ => {}
                    }
                }
                Ok(Number::Integer(n)) => {
                    if let Some(c) = n.to_u32().and_then(std::char::from_u32) {
                        string.push(c);
                        continue;
                    }
                }
                _ => {
                    let err = self.type_error(ValidType::Integer, addr);
                    return Err(self.error_form(err, stub_gen()));
                }
            }

            let err = self.representation_error(RepFlag::CharacterCode);
            return Err(self.error_form(err, stub_gen()));
        }

        Ok(string)
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
                let reg = self.store(self.deref(self.registers[2]));
                let n = match Number::try_from(reg) {
                    Ok(Number::Fixnum(n)) => usize::try_from(n.get_num()).ok(),
                    Ok(Number::Integer(n)) => n.to_usize(),
                    _ => {
                        unreachable!()
                    }
                };

                if let Some(n) = n {
                    if n <= MAX_ARITY {
                        let target = self.registers[n];
                        let addr = self.registers[1];

                        unify_fn!(self, addr, target);
                        return return_from_clause!(self.last_call, self);
                    }
                }

                self.fail = true;
            }
            &SystemClauseType::CurrentHostname => {
                match hostname::get().ok() {
                    Some(host) => match host.to_str() {
                        Some(host) => {
                            let hostname = self.atom_tbl.build_with(host);

                            self.unify_atom(hostname, self.store(self.deref(self.registers[1])));
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
                let addr = self.store(self.deref(self.registers[1]));
                let stream = *current_input_stream;

                if let Some(var) = addr.as_var() {
                    self.bind(var, stream_as_cell!(stream));
                    return return_from_clause!(self.last_call, self);
                }

                read_heap_cell!(addr,
                    (HeapCellValueTag::Cons, cons_ptr) => {
                        match_untyped_arena_ptr!(cons_ptr,
                             (ArenaHeaderTag::Stream, other_stream) => {
                                 self.fail = stream != other_stream;
                             }
                             _ => {
                                 let stub = functor_stub(atom!("current_input"), 1);
                                 let err = self.domain_error(DomainErrorType::Stream, addr);

                                 return Err(self.error_form(err, stub));
                             }
                        );
                    }
                    _ => {
                        let stub = functor_stub(atom!("current_input"), 1);
                        let err = self.domain_error(DomainErrorType::Stream, addr);

                        return Err(self.error_form(err, stub));
                    }
                );
            }
            &SystemClauseType::CurrentOutput => {
                let addr = self.store(self.deref(self.registers[1]));
                let stream = *current_output_stream;

                if let Some(var) = addr.as_var() {
                    self.bind(var, stream_as_cell!(stream));
                    return return_from_clause!(self.last_call, self);
                }

                read_heap_cell!(addr,
                    (HeapCellValueTag::Cons, cons_ptr) => {
                        match_untyped_arena_ptr!(cons_ptr,
                             (ArenaHeaderTag::Stream, other_stream) => {
                                 self.fail = stream != other_stream;
                             }
                             _ => {
                                 let stub = functor_stub(atom!("current_output"), 1);
                                 let err = self.domain_error(DomainErrorType::Stream, addr);

                                 return Err(self.error_form(err, stub));
                             }
                        );
                    }
                    _ => {
                        let stub = functor_stub(atom!("current_output"), 1);
                        let err = self.domain_error(DomainErrorType::Stream, addr);

                        return Err(self.error_form(err, stub));
                    }
                );
            }
            &SystemClauseType::DirectoryFiles => {
                if let Some(dir) = self.value_to_str_like(self.registers[1]) {
                    let path = std::path::Path::new(dir.as_str());
                    let mut files = Vec::new();

                    if let Ok(entries) = fs::read_dir(path) {
                        for entry in entries {
                            if let Ok(entry) = entry {
                                if let Some(name) = entry.file_name().to_str() {
                                    let name = self.atom_tbl.build_with(name);
                                    files.push(atom_as_cstr_cell!(name));

                                    continue;
                                }
                            }

                            let stub = functor_stub(atom!("directory_files"), 2);
                            let err = self.representation_error(RepFlag::Character);
                            let err = self.error_form(err, stub);

                            return Err(err);
                        }

                        let files_list = heap_loc_as_cell!(
                            iter_to_heap_list(&mut self.heap, files.into_iter())
                        );

                        unify!(self, self.registers[2], files_list);
                        return return_from_clause!(self.last_call, self);
                    }
                }

                self.fail = true;
            }
            &SystemClauseType::FileSize => {
                if let Some(file) = self.value_to_str_like(self.registers[1]) {
                    let len = Number::arena_from(
                        fs::metadata(file.as_str()).unwrap().len(),
                        &mut self.arena,
                    );

                    match len {
                        Number::Fixnum(n) => self.unify_fixnum(n, self.registers[2]),
                        Number::Integer(n) => self.unify_big_int(n, self.registers[2]),
                        _ => unreachable!(),
                    }
                } else {
                    self.fail = true;
                }
            }
            &SystemClauseType::FileExists => {
                if let Some(file) = self.value_to_str_like(self.registers[1]) {
                    let file_str = file.as_str();

                    if !std::path::Path::new(file_str).exists() || !fs::metadata(file_str).unwrap().is_file() {
                        self.fail = true;
                    }
                } else {
                    self.fail = true;
                }
            }
            &SystemClauseType::DirectoryExists => {
                if let Some(dir) = self.value_to_str_like(self.registers[1]) {
                    let dir_str = dir.as_str();

                    if !std::path::Path::new(dir_str).exists()
                        || !fs::metadata(dir_str).unwrap().is_dir()
                    {
                        self.fail = true;
                        return Ok(());
                    }
                } else {
                    self.fail = true;
                }
            }
            &SystemClauseType::DirectorySeparator => {
                self.unify_char(std::path::MAIN_SEPARATOR, self.registers[1]);
            }
            &SystemClauseType::MakeDirectory => {
                if let Some(dir) = self.value_to_str_like(self.registers[1]) {
                    match fs::create_dir(dir.as_str()) {
                        Ok(_) => {}
                        _ => {
                            self.fail = true;
                            return Ok(());
                        }
                    }
                } else {
                    self.fail = true;
                }
            }
            &SystemClauseType::MakeDirectoryPath => {
                if let Some(dir) = self.value_to_str_like(self.registers[1]) {

                    match fs::create_dir_all(dir.as_str()) {
                        Ok(_) => {}
                        _ => {
                            self.fail = true;
                            return Ok(());
                        }
                    }
                } else {
                    self.fail = true;
                }
            }
            &SystemClauseType::DeleteFile => {
                if let Some(file) = self.value_to_str_like(self.registers[1]) {
                    match fs::remove_file(file.as_str()) {
                        Ok(_) => {}
                        _ => {
                            self.fail = true;
                            return Ok(());
                        }
                    }
                }
            }
            &SystemClauseType::RenameFile => {
                if let Some(file) = self.value_to_str_like(self.registers[1]) {
                    if let Some(renamed) = self.value_to_str_like(self.registers[2]) {
                        if fs::rename(file.as_str(), renamed.as_str()).is_ok() {
                            return return_from_clause!(self.last_call, self);
                        }
                    }
                }

                self.fail = true;
            }
            &SystemClauseType::DeleteDirectory => {
                if let Some(dir) = self.value_to_str_like(self.registers[1]) {
                    match fs::remove_dir(dir.as_str()) {
                        Ok(_) => {}
                        _ => {
                            self.fail = true;
                            return Ok(());
                        }
                    }
                }
            }
            &SystemClauseType::WorkingDirectory => {
                if let Ok(dir) = env::current_dir() {
                    let current = match dir.to_str() {
                        Some(d) => d,
                        _ => {
                            let stub = functor_stub(atom!("working_directory"), 2);
                            let err = self.representation_error(RepFlag::Character);
                            let err = self.error_form(err, stub);

                            return Err(err);
                        }
                    };

                    let current_atom = self.atom_tbl.build_with(&current);

                    self.unify_complete_string(
                        current_atom,
                        self.store(self.deref(self.registers[1])),
                    );

                    if self.fail {
                        return Ok(());
                    }

                    if let Some(next) = self.value_to_str_like(self.registers[2]) {
                        if env::set_current_dir(std::path::Path::new(next.as_str())).is_ok() {
                            return return_from_clause!(self.last_call, self);
                        }
                    }
                }

                self.fail = true;
            }
            &SystemClauseType::PathCanonical => {
                if let Some(path) = self.value_to_str_like(self.registers[1]) {
                    match fs::canonicalize(path.as_str()) {
                        Ok(canonical) => {
                            let cs = match canonical.to_str() {
                                Some(s) => s,
                                _ => {
                                    let stub = functor_stub(atom!("path_canonical"), 2);
                                    let err = self.representation_error(RepFlag::Character);
                                    let err = self.error_form(err, stub);

                                    return Err(err);
                                }
                            };

                            let canonical_atom = self.atom_tbl.build_with(cs);

                            self.unify_complete_string(
                                canonical_atom,
                                self.store(self.deref(self.registers[2])),
                            );

                            return return_from_clause!(self.last_call, self);
                        }
                        _ => {
                        }
                    }
                }

                self.fail = true;
            }
            &SystemClauseType::FileTime => {
                if let Some(file) = self.value_to_str_like(self.registers[1]) {
                    let which = cell_as_atom!(self.store(self.deref(self.registers[2])));

                    if let Ok(md) = fs::metadata(file.as_str()) {
                        if let Ok(time) = match which {
                            atom!("modification") => md.modified(),
                            atom!("access") => md.accessed(),
                            atom!("creation") => md.created(),
                            _ => {
                                unreachable!()
                            }
                        } {
                            let chars_atom = self.systemtime_to_timestamp(time);

                            self.unify_complete_string(
                                chars_atom,
                                self.registers[3],
                            );

                            return return_from_clause!(self.last_call, self);
                        }
                    }
                }

                self.fail = true;
            }
            &SystemClauseType::AtomChars => {
                let a1 = self.store(self.deref(self.registers[1]));

                read_heap_cell!(a1,
                    (HeapCellValueTag::Char) => {
                        let h = self.heap.len();

                        self.heap.push(a1);
                        self.heap.push(empty_list_as_cell!());

                        unify!(self, self.registers[2], list_loc_as_cell!(h));
                    }
                    (HeapCellValueTag::Atom, (name, arity)) => {
                        if arity == 0 {
                            self.unify_complete_string(
                                name,
                                self.store(self.deref(self.registers[2])),
                            );
                        } else {
                            self.fail = true;
                        }
                    }
                    (HeapCellValueTag::Var | HeapCellValueTag::AttrVar | HeapCellValueTag::StackVar) => {
                        let a2 = self.store(self.deref(self.registers[2]));

                        if let Some(str_like) = self.value_to_str_like(a2) {
                            let atom = match str_like {
                                AtomOrString::Atom(atom) => {
                                    atom
                                }
                                AtomOrString::String(string) => {
                                    self.atom_tbl.build_with(&string)
                                }
                            };

                            self.bind(a1.as_var().unwrap(), atom_as_cell!(atom));
                            return return_from_clause!(self.last_call, self);
                        }

                        self.fail = true;
                    }
                    _ => {
                        unreachable!();
                    }
                );
            }
            &SystemClauseType::AtomCodes => {
                let a1 = self.store(self.deref(self.registers[1]));

                read_heap_cell!(a1,
                    (HeapCellValueTag::Char, c) => {
                        let h = self.heap.len();

                        self.heap.push(fixnum_as_cell!(Fixnum::build_with(c as i64)));
                        self.heap.push(empty_list_as_cell!());

                        unify!(self, list_loc_as_cell!(h), self.registers[2]);
                    }
                    (HeapCellValueTag::Atom, (name, arity)) => {
                        if arity == 0 {
                            let iter = name.chars()
                                .map(|c| fixnum_as_cell!(Fixnum::build_with(c as i64)));

                            let h = iter_to_heap_list(&mut self.heap, iter);
                            unify!(self, heap_loc_as_cell!(h), self.registers[2]);
                        } else {
                            self.fail = true;
                        }
                    }
                    (HeapCellValueTag::Var | HeapCellValueTag::AttrVar | HeapCellValueTag::StackVar) => {
                        let stub_gen = || functor_stub(atom!("atom_codes"), 2);

                        match self.try_from_list(self.registers[2], stub_gen) {
                            Ok(addrs) => {
                                let string = self.codes_to_string(addrs.into_iter(), stub_gen)?;
                                let atom = self.atom_tbl.build_with(&string);

                                self.bind(a1.as_var().unwrap(), atom_as_cell!(atom));
                            }
                            Err(e) => {
                                return Err(e);
                            }
                        }
                    }
                    _ => {
                        unreachable!();
                    }
                );
            }
            &SystemClauseType::AtomLength => {
                let a1 = self.store(self.deref(self.registers[1]));

                let len: i64 = read_heap_cell!(a1,
                    (HeapCellValueTag::Atom, (name, arity)) => {
                        if arity == 0 {
                            name.chars().count() as i64
                        } else {
                            self.fail = true;
                            return Ok(());
                        }
                    }
                    (HeapCellValueTag::Char) => {
                        1
                    }
                    _ => {
                        unreachable!()
                    }
                );

                self.unify_fixnum(
                    Fixnum::build_with(len),
                    self.store(self.deref(self.registers[2])),
                );
            }
            &SystemClauseType::CallContinuation => {
                let stub_gen = || functor_stub(atom!("call_continuation"), 1);
                let a1 = self.store(self.deref(self.registers[1]));

                match self.try_from_list(a1, stub_gen) {
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
                let stub_gen = || functor_stub(atom!("number_chars"), 2);
                let a1 = self.store(self.deref(self.registers[1]));

                if let Some(atom_or_string) = self.value_to_str_like(a1) {
                    self.parse_number_from_string(atom_or_string.to_string(), indices, stub_gen)?;
                } else {
                    // a1 is a ground list at the call site within
                    // number_chars/2, so failure of value_to_str_like
                    // means the list contains a non-character.
                    let err = self.type_error(ValidType::Character, a1);
                    return Err(self.error_form(err, stub_gen()));
                }
            }
            &SystemClauseType::CreatePartialString => {
                let atom = cell_as_atom!(self.store(self.deref(self.registers[1])));

                if atom == atom!("") {
                    self.fail = true;
                    return Ok(());
                }

                let pstr_h = self.heap.len();

                self.heap.push(pstr_as_cell!(atom));
                self.heap.push(heap_loc_as_cell!(pstr_h+1));

                unify!(self, self.registers[2], pstr_loc_as_cell!(pstr_h));

                if !self.fail {
                    self.bind(Ref::heap_cell(pstr_h+1), self.registers[3]);
                }
            }
            &SystemClauseType::IsPartialString => {
                let value = self.store(self.deref(self.registers[1]));

                let h = self.heap.len();
                self.heap.push(value);

                let mut iter = HeapPStrIter::new(&self.heap, h);

                while let Some(_) = iter.next() {}

                let at_end_of_pstr = iter.focus.is_var() || iter.at_string_terminator();
                self.fail = !at_end_of_pstr;

                self.heap.pop();
            }
            &SystemClauseType::PartialStringTail => {
                let pstr = self.store(self.deref(self.registers[1]));

                read_heap_cell!(pstr,
                    (HeapCellValueTag::PStrLoc, h) => {
                        let (h, _) = pstr_loc_and_offset(&self.heap, h);

                        if HeapCellValueTag::CStr == self.heap[h].get_tag() {
                            self.unify_atom(atom!("[]"), self.store(self.deref(self.registers[2])));
                        } else {
                            unify_fn!(self, heap_loc_as_cell!(h+1), self.registers[2]);
                        }
                    }
                    (HeapCellValueTag::CStr) => {
                        self.unify_atom(atom!("[]"), self.store(self.deref(self.registers[2])));
                    }
                    (HeapCellValueTag::Lis, h) => {
                        unify_fn!(self, heap_loc_as_cell!(h+1), self.registers[2]);
                    }
                    _ => {
                        self.fail = true;
                    }
                );
            }
            &SystemClauseType::PeekByte => {
                let stub_gen = || functor_stub(atom!("peek_byte"), 2);

                let mut stream = self.get_stream_or_alias(
                    self.registers[1],
                    &indices.stream_aliases,
                    atom!("peek_byte"),
                    2,
                )?;

                self.check_stream_properties(
                    stream,
                    StreamType::Binary,
                    Some(self.registers[2]),
                    atom!("peek_byte"),
                    2,
                )?;

                if stream.past_end_of_stream() {
                    if EOFAction::Reset != stream.options().eof_action() {
                        return return_from_clause!(self.last_call, self);
                    } else if self.fail {
                        return Ok(());
                    }
                }

                if stream.at_end_of_stream() {
                    stream.set_past_end_of_stream(true);

                    self.unify_fixnum(
                        Fixnum::build_with(-1),
                        self.store(self.deref(self.registers[2])),
                    );

                    return return_from_clause!(self.last_call, self);
                }

                let addr = match self.store(self.deref(self.registers[2])) {
                    addr if addr.is_var() => addr,
                    addr => match Number::try_from(addr) {
                        Ok(Number::Integer(n)) => {
                            if let Some(nb) = n.to_u8() {
                                fixnum_as_cell!(Fixnum::build_with(nb as i64))
                            } else {
                                let err = self.type_error(ValidType::InByte, addr);
                                return Err(self.error_form(err, stub_gen()));
                            }
                        }
                        Ok(Number::Fixnum(n)) => {
                            if let Ok(nb) = u8::try_from(n.get_num()) {
                                fixnum_as_cell!(Fixnum::build_with(nb as i64))
                            } else {
                                let err = self.type_error(ValidType::InByte, addr);
                                return Err(self.error_form(err, stub_gen()));
                            }
                        }
                        _ => {
                            let err = self.type_error(ValidType::InByte, addr);
                            return Err(self.error_form(err, stub_gen()));
                        }
                    },
                };

                loop {
                    match stream.peek_byte().map_err(|e| e.kind()) {
                        Ok(b) => {
                            self.unify_fixnum(Fixnum::build_with(b as i64), addr);
                        }
                        Err(ErrorKind::PermissionDenied) => {
                            self.fail = true;
                            break;
                        }
                        _ => {
                            self.eof_action(
                                self.registers[2],
                                stream,
                                atom!("peek_byte"),
                                2,
                            )?;

                            if EOFAction::Reset != stream.options().eof_action() {
                                return return_from_clause!(self.last_call, self);
                            } else if self.fail {
                                return Ok(());
                            }
                        }
                    }
                }
            }
            &SystemClauseType::PeekChar => {
                let stub_gen = || functor_stub(atom!("peek_char"), 2);

                let mut stream = self.get_stream_or_alias(
                    self.registers[1],
                    &indices.stream_aliases,
                    atom!("peek_char"),
                    2,
                )?;

                self.check_stream_properties(
                    stream,
                    StreamType::Text,
                    Some(self.registers[2]),
                    atom!("peek_char"),
                    2,
                )?;

                if stream.past_end_of_stream() {
                    if EOFAction::Reset != stream.options().eof_action() {
                        return return_from_clause!(self.last_call, self);
                    } else if self.fail {
                        return Ok(());
                    }
                }

                if stream.at_end_of_stream() {
                    let end_of_file = atom!("end_of_file");
                    stream.set_past_end_of_stream(true);

                    self.unify_atom(end_of_file, self.store(self.deref(self.registers[2])));
                    return return_from_clause!(self.last_call, self);
                }

                let a2 = self.store(self.deref(self.registers[2]));

                let a2 = read_heap_cell!(a2,
                    (HeapCellValueTag::Char) => {
                        a2
                    }
                    (HeapCellValueTag::Atom, (name, arity)) => {
                        if arity == 0 {
                            if let Some(c) = name.as_char() {
                                char_as_cell!(c)
                            } else {
                                let err = self.type_error(ValidType::InCharacter, a2);
                                return Err(self.error_form(err, stub_gen()));
                            }
                        } else {
                            let err = self.type_error(ValidType::InCharacter, a2);
                            return Err(self.error_form(err, stub_gen()));
                        }
                    }
                    (HeapCellValueTag::Var | HeapCellValueTag::StackVar | HeapCellValueTag::AttrVar) => {
                        a2
                    }
                    _ => {
                        let err = self.type_error(ValidType::InCharacter, a2);
                        return Err(self.error_form(err, stub_gen()));
                    }
                );

                loop {
                    match stream.peek_char().map(|result| result.map_err(|e| e.kind())) {
                        Some(Ok(d)) => {
                            self.unify_char(d, a2);
                        }
                        Some(Err(ErrorKind::PermissionDenied)) => {
                            self.fail = true;
                            break;
                        }
                        _ => {
                            self.eof_action(
                                self.registers[2],
                                stream,
                                atom!("peek_char"),
                                2,
                            )?;

                            if EOFAction::Reset != stream.options().eof_action() {
                                return return_from_clause!(self.last_call, self);
                            } else if self.fail {
                                return Ok(());
                            }
                        }
                    }
                }
            }
            &SystemClauseType::PeekCode => {
                let stub_gen = || functor_stub(atom!("peek_code"), 2);

                let mut stream = self.get_stream_or_alias(
                    self.registers[1],
                    &indices.stream_aliases,
                    atom!("peek_code"),
                    2,
                )?;

                self.check_stream_properties(
                    stream,
                    StreamType::Text,
                    Some(self.registers[2]),
                    atom!("peek_code"),
                    2,
                )?;

                if stream.past_end_of_stream() {
                    if EOFAction::Reset != stream.options().eof_action() {
                        return return_from_clause!(self.last_call, self);
                    } else if self.fail {
                        return Ok(());
                    }
                }

                if stream.at_end_of_stream() {
                    let end_of_file = atom!("end_of_file");
                    stream.set_past_end_of_stream(true);

                    self.unify_atom(end_of_file, self.store(self.deref(self.registers[2])));
                    return return_from_clause!(self.last_call, self);
                }

                let a2 = self.store(self.deref(self.registers[2]));

                let addr = read_heap_cell!(a2,
                    (HeapCellValueTag::Var | HeapCellValueTag::StackVar | HeapCellValueTag::AttrVar) => {
                        a2
                    }
                    _ => {
                        match Number::try_from(a2) {
                            Ok(Number::Integer(n)) => {
                                let n = n
                                    .to_u32()
                                    .and_then(|n| std::char::from_u32(n).and_then(|_| Some(n)));

                                if let Some(n) = n {
                                    fixnum_as_cell!(Fixnum::build_with(n as i64))
                                } else {
                                    let err = self.representation_error(RepFlag::InCharacterCode);
                                    return Err(self.error_form(err, stub_gen()));
                                }
                            }
                            Ok(Number::Fixnum(n)) => {
                                let n = u32::try_from(n.get_num())
                                    .ok()
                                    .and_then(|n| std::char::from_u32(n).and_then(|_| Some(n)));

                                if let Some(n) = n {
                                    fixnum_as_cell!(Fixnum::build_with(n as i64))
                                } else {
                                    let err = self.representation_error(RepFlag::InCharacterCode);
                                    return Err(self.error_form(err, stub_gen()));
                                }
                            }
                            _ => {
                                let err = self.type_error(ValidType::Integer, self.registers[2]);
                                return Err(self.error_form(err, stub_gen()));
                            }
                        }
                    }
                );

                loop {
                    let result = stream.peek_char();

                    match result.map(|result| result.map_err(|e| e.kind())) {
                        Some(Ok(c)) => {
                            self.unify_fixnum(Fixnum::build_with(c as i64), addr);
                        }
                        Some(Err(ErrorKind::PermissionDenied)) => {
                            self.fail = true;
                            break;
                        }
                        _ => {
                            self.eof_action(
                                self.registers[2],
                                stream,
                                atom!("peek_code"),
                                2,
                            )?;

                            if EOFAction::Reset != stream.options().eof_action() {
                                return return_from_clause!(self.last_call, self);
                            } else if self.fail {
                                return Ok(());
                            }
                        }
                    }
                }
            }
            &SystemClauseType::NumberToChars => {
                let n = self.registers[1];
                let chs = self.registers[2];

                let n = self.store(self.deref(n));

                let string = match Number::try_from(n) {
                    Ok(Number::Float(OrderedFloat(n))) => {
                        format!("{0:<20?}", n)
                    }
                    Ok(Number::Fixnum(n)) => n.get_num().to_string(),
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

                let chars_atom = self.atom_tbl.build_with(&string.trim());
                self.unify_complete_string(chars_atom, self.store(self.deref(chs)));
            }
            &SystemClauseType::NumberToCodes => {
                let n = self.store(self.deref(self.registers[1]));
                let chs = self.registers[2];

                let string = match Number::try_from(n) {
                    Ok(Number::Float(OrderedFloat(n))) => {
                        format!("{0:<20?}", n)
                    }
                    Ok(Number::Fixnum(n)) => n.get_num().to_string(),
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

                let codes = string.trim().chars().map(|c| {
                    fixnum_as_cell!(Fixnum::build_with(c as i64))
                });

                let h = iter_to_heap_list(&mut self.heap, codes);
                unify!(self, heap_loc_as_cell!(h), chs);
            }
            &SystemClauseType::CodesToNumber => {
                let stub_gen = || functor_stub(atom!("number_codes"), 2);

                match self.try_from_list(self.registers[1], stub_gen) {
                    Err(e) => {
                        return Err(e);
                    }
                    Ok(addrs) => {
                        let string = self.codes_to_string(addrs.into_iter(), stub_gen)?;
                        self.parse_number_from_string(string, indices, stub_gen)?;
                    }
                }
            }
            &SystemClauseType::LiftedHeapLength => {
                let a1 = self.registers[1];
                let lh_len = Fixnum::build_with(self.lifted_heap.len() as i64);

                self.unify_fixnum(lh_len, a1);
            }
            &SystemClauseType::CharCode => {
                let stub_gen = || functor_stub(atom!("char_code"), 2);
                let a1 = self.store(self.deref(self.registers[1]));

                let c = read_heap_cell!(a1,
                    (HeapCellValueTag::Atom, (name, _arity)) => {
                        name.as_char().unwrap()
                    }
                    (HeapCellValueTag::Char, c) => {
                        c
                    }
                    _ => {
                        let a2 = self.store(self.deref(self.registers[2]));

                        match Number::try_from(a2) {
                            Ok(Number::Integer(n)) => {
                                let c = match n.to_u32().and_then(std::char::from_u32) {
                                    Some(c) => c,
                                    _ => {
                                        let err = self.representation_error(RepFlag::CharacterCode);
                                        return Err(self.error_form(err, stub_gen()));
                                    }
                                };

                                self.unify_char(c, a2);
                                return return_from_clause!(self.last_call, self);
                            }
                            Ok(Number::Fixnum(n)) => {
                                match u32::try_from(n.get_num()) {
                                    Ok(n) => {
                                        if let Some(c) = std::char::from_u32(n) {
                                            self.unify_char(c, a1);
                                            return return_from_clause!(self.last_call, self);
                                        }
                                    }
                                    _ => {}
                                }

                                let err = self.representation_error(RepFlag::CharacterCode);
                                return Err(self.error_form(err, stub_gen()));
                            }
                            _ => {
                                self.fail = true;
                                return Ok(());
                            }
                        }
                    }
                );

                self.unify_fixnum(
                    Fixnum::build_with(c as i64),
                    self.store(self.deref(self.registers[2])),
                );
            }
            &SystemClauseType::CharType => {
                let a1 = self.store(self.deref(self.registers[1]));
                let a2 = self.store(self.deref(self.registers[2]));

                let c = read_heap_cell!(a1,
                    (HeapCellValueTag::Char, c) => {
                        c
                    }
                    (HeapCellValueTag::Atom, (name, _arity)) => {
                        name.as_char().unwrap()
                    }
                    _ => {
                        unreachable!()
                    }
                );

                let chars = cell_as_atom!(a2);
                self.fail = true; // This predicate fails by default.

                macro_rules! macro_check {
                    ($id:ident, $name:expr) => {
                        if $id!(c) && chars == $name {
                            self.fail = false;
                            return return_from_clause!(self.last_call, self);
                        }
                    };
                }

                macro_rules! method_check {
                    ($id:ident, $name:expr) => {
                        if c.$id() && chars == $name {
                            self.fail = false;
                            return return_from_clause!(self.last_call, self);
                        }
                    };
                }

                macro_check!(alpha_char, atom!("alpha"));
                method_check!(is_alphabetic, atom!("alphabetic"));
                method_check!(is_alphanumeric, atom!("alphanumeric"));
                macro_check!(alpha_numeric_char, atom!("alnum"));
                method_check!(is_ascii, atom!("ascii"));
                method_check!(is_ascii_punctuation, atom!("ascii_ponctuaction"));
                method_check!(is_ascii_graphic, atom!("ascii_graphic"));
                // macro_check!(backslash_char, atom!("backslash"));
                // macro_check!(back_quote_char, atom!("back_quote"));
                macro_check!(binary_digit_char, atom!("binary_digit"));
                // macro_check!(capital_letter_char, atom!("upper"));
                // macro_check!(comment_1_char, "comment_1");
                // macro_check!(comment_2_char, "comment_2");
                method_check!(is_control, atom!("control"));
                // macro_check!(cut_char, atom!("cut"));
                macro_check!(decimal_digit_char, atom!("decimal_digit"));
                // macro_check!(decimal_point_char, atom!("decimal_point"));
                // macro_check!(double_quote_char, atom!("double_quote"));
                macro_check!(exponent_char, atom!("exponent"));
                macro_check!(graphic_char, atom!("graphic"));
                macro_check!(graphic_token_char, atom!("graphic_token"));
                macro_check!(hexadecimal_digit_char, atom!("hexadecimal_digit"));
                macro_check!(layout_char, atom!("layout"));
                method_check!(is_lowercase, atom!("lower"));
                macro_check!(meta_char, atom!("meta"));
                // macro_check!(new_line_char, atom!("new_line"));
                method_check!(is_numeric, atom!("numeric"));
                macro_check!(octal_digit_char, atom!("octal_digit"));
                macro_check!(octet_char, atom!("octet"));
                macro_check!(prolog_char, atom!("prolog"));
                // macro_check!(semicolon_char, atom!("semicolon"));
                macro_check!(sign_char, atom!("sign"));
                // macro_check!(single_quote_char, atom!("single_quote"));
                // macro_check!(small_letter_char, atom!("lower"));
                macro_check!(solo_char, atom!("solo"));
                // macro_check!(space_char, atom!("space"));
                macro_check!(symbolic_hexadecimal_char, atom!("symbolic_hexadecimal"));
                macro_check!(symbolic_control_char, atom!("symbolic_control"));
                method_check!(is_uppercase, atom!("upper"));
                // macro_check!(variable_indicator_char, atom!("variable_indicator"));
                method_check!(is_whitespace, atom!("whitespace"));
            }
            &SystemClauseType::CheckCutPoint => {
                let addr = self.store(self.deref(self.registers[1]));
                let old_b = cell_as_fixnum!(addr).get_num() as usize;

                let prev_b = self.stack.index_or_frame(self.b).prelude.b;
                let prev_b = self.stack.index_or_frame(prev_b).prelude.b;

                if prev_b > old_b {
                    self.fail = true;
                }
            }
            &SystemClauseType::CopyTermWithoutAttrVars => {
                self.copy_term(AttrVarPolicy::StripAttributes);
            }
            &SystemClauseType::FetchGlobalVar => {
                let key = cell_as_atom!(self.store(self.deref(self.registers[1])));
                let addr = self.registers[2];

                match indices.global_variables.get_mut(&key) {
                    Some((ref ball, ref mut loc)) => match loc {
                        Some(value_loc) => {
                            unify_fn!(self, addr, *value_loc);
                        }
                        None if !ball.stub.is_empty() => {
                            let h = self.heap.len();
                            let stub = ball.copy_and_align(h);

                            self.heap.extend(stub.into_iter());

                            unify_fn!(self, addr, heap_loc_as_cell!(h));

                            if !self.fail {
                                *loc = Some(heap_loc_as_cell!(h));
                                self.trail(TrailRef::BlackboardEntry(key));
                            }
                        }
                        _ => self.fail = true,
                    },
                    None => self.fail = true,
                };
            }
            &SystemClauseType::PutCode => {
                let mut stream = self.get_stream_or_alias(
                    self.registers[1],
                    &indices.stream_aliases,
                    atom!("put_code"),
                    2,
                )?;

                self.check_stream_properties(
                    stream,
                    StreamType::Text,
                    None,
                    atom!("put_code"),
                    2,
                )?;

                let stub_gen = || functor_stub(atom!("put_code"), 2);

                let addr = self.store(self.deref(self.registers[2]));

                if addr.is_var() {
                    let err = self.instantiation_error();
                    return Err(self.error_form(err, stub_gen()));
                } else {
                    match Number::try_from(addr) {
                        Ok(Number::Integer(n)) => {
                            if let Some(c) = n.to_u32().and_then(|c| char::try_from(c).ok()) {
                                write!(&mut stream, "{}", c).unwrap();
                                return return_from_clause!(self.last_call, self);
                            }
                        }
                        Ok(Number::Fixnum(n)) => {
                            let n = n.get_num();

                            if let Some(c) = u32::try_from(n).ok().and_then(|c| char::from_u32(c)) {
                                write!(&mut stream, "{}", c).unwrap();
                                return return_from_clause!(self.last_call, self);
                            }
                        }
                        _ => {
                            let err = self.type_error(ValidType::Integer, addr);
                            return Err(self.error_form(err, stub_gen()));
                        }
                    }

                    let err = self.representation_error(RepFlag::CharacterCode);
                    return Err(self.error_form(err, stub_gen()));
                }
            }
            &SystemClauseType::PutChar => {
                let mut stream = self.get_stream_or_alias(
                    self.registers[1],
                    &indices.stream_aliases,
                    atom!("put_char"),
                    2,
                )?;

                self.check_stream_properties(
                    stream,
                    StreamType::Text,
                    None,
                    atom!("put_char"),
                    2,
                )?;

                let stub_gen = || functor_stub(atom!("put_char"), 2);
                let addr = self.store(self.deref(self.registers[2]));

                if addr.is_var() {
                    let err = self.instantiation_error();
                    return Err(self.error_form(err, stub_gen()));
                } else {
                    read_heap_cell!(addr,
                        (HeapCellValueTag::Atom, (name, _arity)) => {
                            let c = name.as_char().unwrap();
                            write!(&mut stream, "{}", c).unwrap();
                            return return_from_clause!(self.last_call, self);
                        }
                        (HeapCellValueTag::Char, c) => {
                            write!(&mut stream, "{}", c).unwrap();
                            return return_from_clause!(self.last_call, self);
                        }
                        _ => {
                        }
                    );

                    let err = self.type_error(ValidType::Character, addr);
                    return Err(self.error_form(err, stub_gen()));
                }
            }
            &SystemClauseType::PutChars => {
                let mut stream = self.get_stream_or_alias(
                    self.registers[1],
                    &indices.stream_aliases,
                    atom!("$put_chars"),
                    2,
                )?;

                let mut bytes = Vec::new();
                let stub_gen = || functor_stub(atom!("$put_chars"), 2);

                if let Some(string) = self.value_to_str_like(self.registers[2]) {
                    if stream.options().stream_type() == StreamType::Binary {
                        for c in string.as_str().chars() {
                            if c as u32 > 255 {
                                let err = self.type_error(ValidType::Byte, char_as_cell!(c));
                                return Err(self.error_form(err, stub_gen()));
                            }

                            bytes.push(c as u8);
                        }
                    } else {
                        bytes = string.as_str().bytes().collect();
                    }

                    match stream.write_all(&bytes) {
                        Ok(_) => {
                            return return_from_clause!(self.last_call, self);
                        }
                        _ => {
                            let addr = stream_as_cell!(stream);
                            let err = self.existence_error(ExistenceError::Stream(addr));

                            return Err(self.error_form(err, stub_gen()));
                        }
                    }
                } else {
                    self.fail = true;
                }
            }
            &SystemClauseType::PutByte => {
                let mut stream = self.get_stream_or_alias(
                    self.registers[1],
                    &indices.stream_aliases,
                    atom!("put_byte"),
                    2,
                )?;

                self.check_stream_properties(
                    stream,
                    StreamType::Binary,
                    None,
                    atom!("put_byte"),
                    2,
                )?;

                let stub_gen = || functor_stub(atom!("put_byte"), 2);
                let addr = self.store(self.deref(self.registers[2]));

                if addr.is_var() {
                    let err = self.instantiation_error();
                    return Err(self.error_form(err, stub_gen()));
                } else {
                    match Number::try_from(addr) {
                        Ok(Number::Integer(n)) => {
                            if let Some(nb) = n.to_u8() {
                                match stream.write(&mut [nb]) {
                                    Ok(1) => {
                                        return return_from_clause!(self.last_call, self);
                                    }
                                    _ => {
                                        let err = self.existence_error(
                                            ExistenceError::Stream(stream_as_cell!(stream))
                                        );

                                        return Err(self.error_form(err, stub_gen()));
                                    }
                                }
                            }
                        }
                        Ok(Number::Fixnum(n)) => {
                            if let Ok(nb) = u8::try_from(n.get_num()) {
                                match stream.write(&mut [nb]) {
                                    Ok(1) => {
                                        return return_from_clause!(self.last_call, self);
                                    }
                                    _ => {
                                        let err = self.existence_error(
                                            ExistenceError::Stream(stream_as_cell!(stream))
                                        );

                                        return Err(self.error_form(err, stub_gen()));
                                    }
                                }
                            }
                        }
                        _ => {
                        }
                    }
                }

                let err = self.type_error(ValidType::Byte, self.registers[2]);
                return Err(self.error_form(err, stub_gen()));
            }
            &SystemClauseType::GetByte => {
                let mut stream = self.get_stream_or_alias(
                    self.registers[1],
                    &indices.stream_aliases,
                    atom!("get_byte"),
                    2,
                )?;

                self.check_stream_properties(
                    stream,
                    StreamType::Binary,
                    Some(self.registers[2]),
                    atom!("get_byte"),
                    2,
                )?;

                if stream.past_end_of_stream() {
                    self.eof_action(self.registers[2], stream, atom!("get_byte"), 2)?;

                    if EOFAction::Reset != stream.options().eof_action() {
                        return return_from_clause!(self.last_call, self);
                    } else if self.fail {
                        return Ok(());
                    }
                }

                let stub_gen = || functor_stub(atom!("get_byte"), 2);
                let addr = self.store(self.deref(self.registers[2]));

                let addr = if addr.is_var() {
                    addr
                } else {
                    match Number::try_from(addr) {
                        Ok(Number::Integer(n)) => {
                            if let Some(nb) = n.to_u8() {
                                fixnum_as_cell!(Fixnum::build_with(nb as i64))
                            } else {
                                let err = self.type_error(ValidType::InByte, addr);
                                return Err(self.error_form(err, stub_gen()));
                            }
                        }
                        Ok(Number::Fixnum(n)) => {
                            if let Ok(nb) = u8::try_from(n.get_num()) {
                                fixnum_as_cell!(Fixnum::build_with(nb as i64))
                            } else {
                                let err = self.type_error(ValidType::InByte, addr);
                                return Err(self.error_form(err, stub_gen()));
                            }
                        }
                        _ => {
                            let err = self.type_error(ValidType::InByte, addr);
                            return Err(self.error_form(err, stub_gen()));
                        }
                    }
                };

                loop {
                    let mut b = [0u8; 1];

                    match stream.read(&mut b) {
                        Ok(1) => {
                            self.unify_fixnum(Fixnum::build_with(b[0] as i64), addr);
                            break;
                        }
                        _ => {
                            stream.set_past_end_of_stream(true);
                            self.unify_fixnum(Fixnum::build_with(-1), self.registers[2]);
                            return return_from_clause!(self.last_call, self);
                        }
                    }
                }
            }
            &SystemClauseType::GetChar => {
                let mut stream = self.get_stream_or_alias(
                    self.registers[1],
                    &indices.stream_aliases,
                    atom!("get_char"),
                    2,
                )?;

                self.check_stream_properties(
                    stream,
                    StreamType::Text,
                    Some(self.registers[2]),
                    atom!("get_char"),
                    2,
                )?;

                if stream.past_end_of_stream() {
                    if EOFAction::Reset != stream.options().eof_action() {
                        return return_from_clause!(self.last_call, self);
                    } else if self.fail {
                        return Ok(());
                    }
                }

                if stream.at_end_of_stream() {
                    let end_of_file = atom!("end_of_file");
                    stream.set_past_end_of_stream(true);

                    self.unify_atom(end_of_file, self.store(self.deref(self.registers[2])));
                    return return_from_clause!(self.last_call, self);
                }

                let stub_gen = || functor_stub(atom!("get_char"), 2);
                let mut iter = self.open_parsing_stream(stream, atom!("get_char"), 2)?;

                let addr = self.store(self.deref(self.registers[2]));

                let addr = if addr.is_var() {
                    addr
                } else {
                    read_heap_cell!(addr,
                        (HeapCellValueTag::Atom, (atom, _arity)) => {
                            char_as_cell!(atom.as_char().unwrap())
                        }
                        (HeapCellValueTag::Char) => {
                            addr
                        }
                        _ => {
                            let err = self.type_error(ValidType::InCharacter, addr);
                            return Err(self.error_form(err, stub_gen()));
                        }
                    )
                };

                loop {
                    let result = iter.read_char();

                    match result {
                        Some(Ok(c)) => {
                            self.unify_char(c, addr);

                            if self.fail {
                                return Ok(());
                            }

                            break;
                        }
                        _ => {
                            self.eof_action(
                                self.registers[2],
                                stream,
                                atom!("get_char"),
                                2,
                            )?;

                            if EOFAction::Reset != stream.options().eof_action() {
                                return return_from_clause!(self.last_call, self);
                            } else if self.fail {
                                return Ok(());
                            }
                        }
                    }
                }
            }
            &SystemClauseType::GetNChars => {
                let stream = self.get_stream_or_alias(
                    self.registers[1],
                    &indices.stream_aliases,
                    atom!("get_n_chars"),
                    3,
                )?;

                let num = match Number::try_from(self.store(self.deref(self.registers[2]))) {
                    Ok(Number::Fixnum(n)) => usize::try_from(n.get_num()).unwrap(),
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

                if stream.options().stream_type() == StreamType::Binary {
                    let mut buf = vec![];
                    let mut chunk = stream.take(num as u64);

                    chunk.read_to_end(&mut buf).ok();

                    for c in buf {
                        string.push(c as char);
                    }
                } else {
                    let mut iter = self.open_parsing_stream(stream, atom!("get_n_chars"), 2)?;

                    for _ in 0..num {
                        let result = iter.read_char();

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

                let atom = self.atom_tbl.build_with(&string);
                self.unify_complete_string(atom, self.store(self.deref(self.registers[3])));
            }
            &SystemClauseType::GetCode => {
                let mut stream = self.get_stream_or_alias(
                    self.registers[1],
                    &indices.stream_aliases,
                    atom!("get_code"),
                    2,
                )?;

                self.check_stream_properties(
                    stream,
                    StreamType::Text,
                    Some(self.registers[2]),
                    atom!("get_code"),
                    2,
                )?;

                if stream.past_end_of_stream() {
                    if EOFAction::Reset != stream.options().eof_action() {
                        return return_from_clause!(self.last_call, self);
                    } else if self.fail {
                        return Ok(());
                    }
                }

                if stream.at_end_of_stream() {
                    let end_of_file = atom!("end_of_file");

                    stream.set_past_end_of_stream(true);

                    self.unify_atom(end_of_file, self.store(self.deref(self.registers[2])));
                    return return_from_clause!(self.last_call, self);
                }

                let stub_gen = || functor_stub(atom!("get_code"), 2);
                let addr = self.store(self.deref(self.registers[2]));

                let addr = if addr.is_var() {
                    addr
                } else {
                    match Number::try_from(addr) {
                        Ok(Number::Integer(n)) => {
                            let n = n
                                .to_u32()
                                .and_then(|n| std::char::from_u32(n));

                            if let Some(n) = n {
                                fixnum_as_cell!(Fixnum::build_with(n as i64))
                            } else {
                                let err = self.representation_error(RepFlag::InCharacterCode);
                                return Err(self.error_form(err, stub_gen()));
                            }
                        }
                        Ok(Number::Fixnum(n)) => {
                            let nf = u32::try_from(n.get_num())
                                .ok()
                                .and_then(|n| std::char::from_u32(n));

                            if nf.is_some() {
                                fixnum_as_cell!(n)
                            } else {
                                let err = self.representation_error(RepFlag::InCharacterCode);
                                return Err(self.error_form(err, stub_gen()));
                            }
                        }
                        _ => {
                            let err = self.type_error(ValidType::Integer, self.registers[2]);
                            return Err(self.error_form(err, stub_gen()));
                        }
                    }
                };

                let mut iter = self.open_parsing_stream(stream.clone(), atom!("get_code"), 2)?;

                loop {
                    let result = iter.read_char();

                    match result {
                        Some(Ok(c)) => {
                            self.unify_fixnum(Fixnum::build_with(c as i64), addr);

                            if self.fail {
                                return Ok(());
                            }

                            break;
                        }
                        _ => {
                            self.eof_action(
                                self.registers[2],
                                stream,
                                atom!("get_code"),
                                2,
                            )?;

                            if EOFAction::Reset != stream.options().eof_action() {
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
                    let stream = stream_as_cell!(first_stream);

                    let var = self.store(self.deref(self.registers[1])).as_var().unwrap();
                    self.bind(var, stream);
                } else {
                    self.fail = true;
                    return Ok(());
                }
            }
            &SystemClauseType::NextStream => {
                let prev_stream = cell_as_stream!(self.store(self.deref(self.registers[1])));

                let mut next_stream = None;
                let mut null_streams = BTreeSet::new();

                for stream in indices
                    .streams
                    .range(prev_stream..)
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
                    let var = self.store(self.deref(self.registers[2])).as_var().unwrap();
                    let next_stream = stream_as_cell!(next_stream);

                    self.bind(var, next_stream);
                } else {
                    self.fail = true;
                    return Ok(());
                }
            }
            &SystemClauseType::FlushOutput => {
                let mut stream = self.get_stream_or_alias(
                    self.registers[1],
                    &indices.stream_aliases,
                    atom!("flush_output"),
                    1,
                )?;

                if !stream.is_output_stream() {
                    let stub = functor_stub(atom!("flush_output"), 1);
                    let addr = stream_as_cell!(stream); // vec![HeapCellValue::Stream(stream)];

                    let err = self.permission_error(
                        Permission::OutputStream,
                        atom!("stream"),
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
                    let stub = functor_stub(atom!("get_single_char"), 1);
                    let err = self.interrupt_error();
                    let err = self.error_form(err, stub);

                    return Err(err);
                }

                let c = match key.code {
                    KeyCode::Enter => '\n',
                    KeyCode::Tab => '\t',
                    KeyCode::Char(c) => c,
                    _ => unreachable!(),
                };

                self.unify_char(c, self.store(self.deref(self.registers[1])));
            }
            &SystemClauseType::HeadIsDynamic => {
                let module_name = cell_as_atom!(self.store(self.deref(self.registers[1])));

		        let (name, arity) = read_heap_cell!(self.store(self.deref(self.registers[2])),
                    (HeapCellValueTag::Str, s) => {
			            cell_as_atom_cell!(self.heap[s]).get_name_and_arity()
		            }
                    (HeapCellValueTag::Atom, (name, _arity)) => {
			            (name, 0)
		            }
                    _ => {
			            unreachable!()
		            }
		        );

                self.fail = !indices.is_dynamic_predicate(module_name, (name, arity));
            }
            &SystemClauseType::Close => {
                let mut stream = self.get_stream_or_alias(
                    self.registers[1],
                    &indices.stream_aliases,
                    atom!("close"),
                    2,
                )?;

                if !stream.is_input_stream() {
                    stream.flush().unwrap(); // 8.11.6.1b)
                }

                indices.streams.remove(&stream);

                if stream == *current_input_stream {
                    *current_input_stream = indices
                        .stream_aliases
                        .get(&atom!("user_input"))
                        .cloned()
                        .unwrap();

                    indices.streams.insert(*current_input_stream);
                } else if stream == *current_output_stream {
                    *current_output_stream = indices
                        .stream_aliases
                        .get(&atom!("user_output"))
                        .cloned()
                        .unwrap();

                    indices.streams.insert(*current_output_stream);
                }

                if !stream.is_stdin() && !stream.is_stdout() && !stream.is_stderr() {
                    let close_result = stream.close();

                    if let Some(alias) = stream.options().get_alias() {
                        indices.stream_aliases.remove(&alias);
                    }
                    if let Err(_) = close_result {
                        let stub = functor_stub(atom!("close"), 1);
                        let addr = stream_as_cell!(stream);
                        let err  = self.existence_error(ExistenceError::Stream(addr));

                        return Err(self.error_form(err, stub));
                    }
                }
            }
            &SystemClauseType::CopyToLiftedHeap => {
                let lh_offset = cell_as_fixnum!(
                    self.store(self.deref(self.registers[1]))
                ).get_num() as usize;

                let copy_target = self.registers[2];

                let old_threshold = self.copy_findall_solution(lh_offset, copy_target);
                let new_threshold = self.lifted_heap.len() - lh_offset;

                self.lifted_heap[old_threshold] = heap_loc_as_cell!(new_threshold);

                for addr in self.lifted_heap[old_threshold + 1 ..].iter_mut() {
                    *addr -= self.heap.len() + lh_offset;
                }
            },
            &SystemClauseType::DeleteAttribute => {
                let ls0 = self.store(self.deref(self.registers[1]));

                if let HeapCellValueTag::Lis = ls0.get_tag() {
                    let l1 = ls0.get_value();
                    let ls1 = self.store(self.deref(heap_loc_as_cell!(l1 + 1)));

                    if let HeapCellValueTag::Lis = ls1.get_tag() {
                        let l2 = ls1.get_value();

                        let old_addr = self.heap[l1+1];
                        let tail = self.store(self.deref(heap_loc_as_cell!(l2 + 1)));

                        let tail = if tail.is_var() {
                            heap_loc_as_cell!(l1 + 1)
                        } else {
                            tail
                        };

                        let trail_ref = read_heap_cell!(old_addr,
                            (HeapCellValueTag::Var, h) => {
                                TrailRef::AttrVarHeapLink(h)
                            }
                            (HeapCellValueTag::Lis, l) => {
                                TrailRef::AttrVarListLink(l1 + 1, l)
                            }
                            _ => {
                                unreachable!()
                            }
                        );

                        self.heap[l1 + 1] = tail;
                        self.trail(trail_ref);
                    }
                }
            }
            &SystemClauseType::DeleteHeadAttribute => {
                let addr = self.store(self.deref(self.registers[1]));

                debug_assert_eq!(addr.get_tag(), HeapCellValueTag::AttrVar);

                let h = addr.get_value();
                let addr = self.store(self.deref(self.heap[h + 1]));

                debug_assert_eq!(addr.get_tag(), HeapCellValueTag::Lis);

                let l = addr.get_value();
                let tail = self.store(self.deref(heap_loc_as_cell!(l + 1)));

                let tail = if tail.is_var() {
                    self.heap[h] = heap_loc_as_cell!(h);
                    self.trail(TrailRef::Ref(Ref::attr_var(h)));

                    heap_loc_as_cell!(h + 1)
                } else {
                    tail
                };

                self.heap[h + 1] = tail;
                self.trail(TrailRef::AttrVarListLink(h + 1, l));
            }
            &SystemClauseType::DynamicModuleResolution(narity) => {
                let module_name = self.store(self.deref(self.registers[1 + narity]));
                let module_name = cell_as_atom!(module_name);

                let addr = self.store(self.deref(self.registers[2 + narity]));

                read_heap_cell!(addr,
                    (HeapCellValueTag::Str, a) => {
                        let (name, arity) = cell_as_atom_cell!(self.heap[a])
                            .get_name_and_arity();

                        for i in (arity + 1..arity + narity + 1).rev() {
                            self.registers[i] = self.registers[i - arity];
                        }

                        for i in 1..arity + 1 {
                            self.registers[i] = self.heap[a + i];
                        }

                        return self.module_lookup(
                            indices,
                            call_policy,
                            (name, arity + narity),
                            module_name,
                            true,
                            &indices.stream_aliases,
                        );
                    }
                    (HeapCellValueTag::Atom, (name, _arity)) => {
                        return self.module_lookup(
                            indices,
                            call_policy,
                            (name, narity),
                            module_name,
                            true,
                            &indices.stream_aliases,
                        );
                    }
                    (HeapCellValueTag::Char, c) => {
                        let key = (self.atom_tbl.build_with(&c.to_string()), narity);

                        return self.module_lookup(
                            indices,
                            call_policy,
                            key,
                            module_name,
                            true,
                            &indices.stream_aliases,
                        );
                    }
                    _ => {
                        let stub = functor_stub(atom!("(:)"), 2);
                        let err = self.type_error(ValidType::Callable, addr);

                        return Err(self.error_form(err, stub));
                    }
                );
            }
            &SystemClauseType::EnqueueAttributedVar => {
                let addr = self.store(self.deref(self.registers[1]));

		read_heap_cell!(addr,
		    (HeapCellValueTag::AttrVar, h) => {
			self.attr_var_init.attr_var_queue.push(h);
		    }
		    _ => {
		    }
		);
            }
            &SystemClauseType::GetNextDBRef => {
                let a1 = self.store(self.deref(self.registers[1]));

                if let Some(name_var) = a1.as_var() {
                    let mut iter = indices.code_dir.iter();

                    while let Some(((name, arity), _)) = iter.next() {
                        if SystemClauseType::from(*name, *arity).is_some() {
                            continue;
                        }

                        let arity_var = self.deref(self.registers[2])
                            .as_var().unwrap();

                        self.bind(name_var, atom_as_cell!(name));
                        self.bind(arity_var, fixnum_as_cell!(Fixnum::build_with(*arity as i64)));

                        return return_from_clause!(self.last_call, self);
                    }

                    self.fail = true;
                } else if a1.get_tag() == HeapCellValueTag::Atom {
                    let name = cell_as_atom!(a1);
                    let arity = cell_as_fixnum!(self.store(self.deref(self.registers[2])))
                        .get_num() as usize;

                    match self.get_next_db_ref(indices, &DBRef::NamedPred(name, arity)) {
                        Some(DBRef::NamedPred(name, arity)) => {
                            let atom_var = self.deref(self.registers[3])
                                .as_var().unwrap();

                            let arity_var = self.deref(self.registers[4])
                                .as_var().unwrap();

                            self.bind(atom_var, atom_as_cell!(name));
                            self.bind(arity_var, fixnum_as_cell!(Fixnum::build_with(arity as i64)));
                        }
                        Some(DBRef::Op(..)) | None => {
                            self.fail = true;
                        }
                    }
                } else {
                    self.fail = true;
                    return Ok(());
                }
            }
            &SystemClauseType::GetNextOpDBRef => {
                let prec = self.store(self.deref(self.registers[1]));

                if let Some(prec_var) = prec.as_var() {
                    let spec = self.store(self.deref(self.registers[2]));
                    let op = self.store(self.deref(self.registers[3]));
                    let orig_op = self.store(self.deref(self.registers[7]));

                    let spec_num = if spec.get_tag() == HeapCellValueTag::Atom {
                        (match cell_as_atom!(spec) {
                            atom!("xfx") => XFX,
                            atom!("xfy") => XFY,
                            atom!("yfx") => YFX,
                            atom!("fx") => FX,
                            atom!("fy") => FY,
                            atom!("xf") => XF,
                            _ => unreachable!(),
                        }) as u8
                    } else {
                        0
                    };

                    let unossified_op_dir = if !orig_op.is_var() {
                        let orig_op = cell_as_atom!(orig_op);

                        let op_descs = [
                            indices.op_dir.get_key_value(&(orig_op, Fixity::In)),
                            indices.op_dir.get_key_value(&(orig_op, Fixity::Pre)),
                            indices.op_dir.get_key_value(&(orig_op, Fixity::Post)),
                        ];

                        let number_of_keys = op_descs[0].is_some() as usize +
                            op_descs[1].is_some() as usize +
                            op_descs[2].is_some() as usize;

                        match number_of_keys {
                            0 => {
                                self.fail = true;
                                return Ok(());
                            }
                            1 => {
                                for op_desc in op_descs {
                                    if let Some((_, op_desc)) = op_desc {
                                        let (op_prec, op_spec) =
                                            (op_desc.get_prec(), op_desc.get_spec());

                                        let op_spec = match op_spec as u32 {
                                            XFX => atom!("xfx"),
                                            XFY => atom!("xfy"),
                                            YFX => atom!("yfx"),
                                            FX => atom!("fx"),
                                            FY => atom!("fy"),
                                            XF => atom!("xf"),
                                            YF => atom!("yf"),
                                            _ => unreachable!(),
                                        };

                                        let op_prec = Fixnum::build_with(op_prec as i64);

                                        self.unify_fixnum(op_prec, prec);
                                        self.unify_atom(op_spec, spec);
                                    }
                                }

                                return return_from_clause!(self.last_call, self);
                            }
                            _ => {
                                let mut unossified_op_dir = OssifiedOpDir::new();

                                for op_desc in op_descs {
                                    if let Some((key, op_desc)) = op_desc {
                                        let (prec, spec) = (op_desc.get_prec(), op_desc.get_spec());
                                        unossified_op_dir.insert(*key, (prec as usize, spec as Specifier));
                                    }
                                }

                                unossified_op_dir
                            }
                        }
                    } else {
                        let mut unossified_op_dir = OssifiedOpDir::new();

                        unossified_op_dir.extend(indices.op_dir.iter().filter_map(
                            |(key, op_desc)| {
                                let (other_prec, other_spec) = (op_desc.get_prec(), op_desc.get_spec());
                                let name = key.0;

                                if other_prec == 0 {
                                    return None;
                                }

                                if (!orig_op.is_var() && atom_as_cell!(name) != orig_op) ||
                                    (!spec.is_var() && other_spec != spec_num) {
                                        return None;
                                    }

                                Some((*key, (other_prec as usize, other_spec as Specifier)))
                            }
                        ));

                        unossified_op_dir
                    };

                    let ossified_op_dir = arena_alloc!(unossified_op_dir, &mut self.arena);

                    match ossified_op_dir.iter().next() {
                        Some(((op_atom, _), (op_prec, op_spec))) => {
                            let ossified_op_dir_var = self.store(self.deref(self.registers[4]))
                                .as_var().unwrap();

                            let spec_atom = match *op_spec {
                                FX => atom!("fx"),
                                FY => atom!("fy"),
                                XF => atom!("xf"),
                                YF => atom!("yf"),
                                XFX => atom!("xfx"),
                                XFY => atom!("xfy"),
                                YFX => atom!("yfx"),
                                _ => {
                                    self.fail = true;
                                    return Ok(());
                                }
                            };

                            let spec_var = spec.as_var().unwrap();
                            let op_var = op.as_var().unwrap();

                            self.bind(prec_var, fixnum_as_cell!(Fixnum::build_with(*op_prec as i64)));
                            self.bind(spec_var, atom_as_cell!(spec_atom));
                            self.bind(op_var, atom_as_cell!(op_atom));
                            self.bind(ossified_op_dir_var, typed_arena_ptr_as_cell!(ossified_op_dir));
                        }
                        None => {
                            self.fail = true;
                            return Ok(());
                        }
                    }
                } else {
                    let spec = cell_as_atom!(self.store(self.deref(self.registers[2])));
                    let op_atom = cell_as_atom!(self.store(self.deref(self.registers[3])));
                    let ossified_op_dir_cell = self.store(self.deref(self.registers[4]));

                    if ossified_op_dir_cell.is_var() {
                        self.fail = true;
                        return Ok(());
                    }

                    let ossified_op_dir = cell_as_ossified_op_dir!(
                        ossified_op_dir_cell
                    );

                    let fixity = match spec {
                        atom!("xfy") | atom!("yfx") | atom!("xfx") => Fixity::In,
                        atom!("xf") | atom!("yf") => Fixity::Post,
                        atom!("fx") | atom!("fy") => Fixity::Pre,
                        _ => {
                            self.fail = true;
                            return Ok(());
                        }
                    };

                    match self.get_next_db_ref(indices, &DBRef::Op(op_atom, fixity, ossified_op_dir)) {
                        Some(DBRef::Op(op_atom, fixity, ossified_op_dir)) => {
                            let (prec, spec) = ossified_op_dir.get(&(op_atom, fixity)).unwrap();

                            let prec_var = self.deref(self.registers[5])
                                .as_var().unwrap();

                            let spec_var = self.deref(self.registers[6])
                                .as_var().unwrap();

                            let op_var = self.deref(self.registers[7])
                                .as_var().unwrap();

                            let spec_atom = match *spec {
                                FX => atom!("fx"),
                                FY => atom!("fy"),
                                XF => atom!("xf"),
                                YF => atom!("yf"),
                                XFX => atom!("xfx"),
                                XFY => atom!("xfy"),
                                YFX => atom!("yfx"),
                                _ => {
                                    self.fail = true;
                                    return Ok(());
                                }
                            };

                            self.bind(prec_var, fixnum_as_cell!(Fixnum::build_with(*prec as i64)));
                            self.bind(spec_var, atom_as_cell!(spec_atom));
                            self.bind(op_var, atom_as_cell!(op_atom));
                        }
                        Some(DBRef::NamedPred(..)) | None => {
                            self.fail = true;
                        }
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
                let secs = ProcessTime::now().as_duration().as_secs_f64();
                let secs = arena_alloc!(OrderedFloat(secs), &mut self.arena);

                self.unify_f64(secs, self.registers[1]);
            }
            &SystemClauseType::CurrentTime => {
                let timestamp = self.systemtime_to_timestamp(SystemTime::now());
                self.unify_atom(timestamp, self.registers[1]);
            }
            &SystemClauseType::Open => {
                let alias = self.registers[4];
                let eof_action = self.registers[5];
                let reposition = self.registers[6];
                let stream_type = self.registers[7];

                let options  = self.to_stream_options(alias, eof_action, reposition, stream_type);
                let src_sink = self.store(self.deref(self.registers[1]));

                if let Some(atom_or_string) = self.value_to_str_like(src_sink) {
                    let file_spec  = self.atom_tbl.build_with(atom_or_string.as_str());
                    let mut stream = self.stream_from_file_spec(file_spec, indices, &options)?;

                    *stream.options_mut() = options;
                    indices.streams.insert(stream);

                    if let Some(alias) = stream.options().get_alias() {
                        indices.stream_aliases.insert(alias, stream);
                    }

                    let stream_var = self.store(self.deref(self.registers[3]));
                    self.bind(stream_var.as_var().unwrap(), stream_as_cell!(stream));
                } else {
                    let err = self.domain_error(DomainErrorType::SourceSink, src_sink);
                    let stub = functor_stub(atom!("open"), 4);

                    return Err(self.error_form(err, stub));
                }
            }
            &SystemClauseType::OpDeclaration => {
                let priority = self.registers[1];
                let specifier = self.registers[2];
                let op = self.registers[3];

                let priority = self.store(self.deref(priority));

                let priority = match Number::try_from(priority) {
                    Ok(Number::Integer(n)) => n.to_u16().unwrap(),
                    Ok(Number::Fixnum(n)) => u16::try_from(n.get_num()).unwrap(),
                    _ => {
                        unreachable!();
                    }
                };

                let specifier = cell_as_atom_cell!(self.store(self.deref(specifier)))
                    .get_name();

                let op = read_heap_cell!(self.store(self.deref(op)),
                    (HeapCellValueTag::Char) => {
                        self.atom_tbl.build_with(&op.to_string())
                    }
                    (HeapCellValueTag::Atom, (name, _arity)) => {
                        name
                    }
                    _ => {
                        unreachable!()
                    }
                );

                let result = to_op_decl(priority, specifier, op)
                    .map_err(SessionError::from)
                    .and_then(|mut op_decl| {
                        if op_decl.op_desc.get_prec() == 0 {
                            Ok(op_decl.remove(&mut indices.op_dir))
                        } else {
                            let spec = get_op_desc(
                                op_decl.name,
                                &CompositeOpDir::new(&indices.op_dir, None),
                            );

                            op_decl.submit(spec, &mut indices.op_dir)
                        }
                    });

                match result {
                    Ok(()) => {}
                    Err(e) => {
                        // 8.14.3.3 l)
                        let err = self.session_error(e);
                        let stub = functor_stub(atom!("op"), 3);

                        return Err(self.error_form(err, stub));
                    }
                }
            }
            &SystemClauseType::SetStreamOptions => {
                let mut stream = self.get_stream_or_alias(
                    self.registers[1],
                    &indices.stream_aliases,
                    atom!("open"),
                    4,
                )?;

                let alias = self.registers[2];
                let eof_action = self.registers[3];
                let reposition = self.registers[4];
                let stream_type = self.registers[5];

                let options = self.to_stream_options(alias, eof_action, reposition, stream_type);
                *stream.options_mut() = options;
            }
            &SystemClauseType::TruncateIfNoLiftedHeapGrowthDiff => {
                self.truncate_if_no_lifted_heap_diff(|h| heap_loc_as_cell!(h))
            }
            &SystemClauseType::TruncateIfNoLiftedHeapGrowth => {
                self.truncate_if_no_lifted_heap_diff(|_| empty_list_as_cell!())
            }
            &SystemClauseType::GetAttributedVariableList => {
                let attr_var = self.store(self.deref(self.registers[1]));
                let attr_var_list = read_heap_cell!(attr_var,
                    (HeapCellValueTag::AttrVar, h) => {
                        h + 1
                    }
                    (HeapCellValueTag::Var | HeapCellValueTag::StackVar) => {
                        // create an AttrVar in the heap.
                        let h = self.heap.len();

                        self.heap.push(attr_var_as_cell!(h));
                        self.heap.push(heap_loc_as_cell!(h+1));

                        self.bind(Ref::attr_var(h), attr_var);
                        h + 1
                    }
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                );

                let list_addr = self.store(self.deref(self.registers[2]));
                self.bind(Ref::heap_cell(attr_var_list), list_addr);
            }
            &SystemClauseType::GetAttrVarQueueDelimiter => {
                let addr = self.registers[1];
                let value = Fixnum::build_with(self.attr_var_init.attr_var_queue.len() as i64);

                self.unify_fixnum(value, self.store(self.deref(addr)));
            }
            &SystemClauseType::GetAttrVarQueueBeyond => {
                let addr = self.registers[1];
                let addr = self.store(self.deref(addr));

                let b = match Number::try_from(addr) {
                    Ok(Number::Integer(n)) => n.to_usize(),
                    Ok(Number::Fixnum(n)) => usize::try_from(n.get_num()).ok(),
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                };

                if let Some(b) = b {
                    let iter = self.gather_attr_vars_created_since(b);

                    let var_list_addr = heap_loc_as_cell!(
                        iter_to_heap_list(&mut self.heap, iter)
                    );

                    let list_addr = self.registers[2];
                    unify!(self, var_list_addr, list_addr);
                }
            }
            &SystemClauseType::GetContinuationChunk => {
                let e = self.store(self.deref(self.registers[1]));
                let e = cell_as_fixnum!(e).get_num() as usize;

                let p_functor = self.store(self.deref(self.registers[2]));
                let p = to_local_code_ptr(&self.heap, p_functor).unwrap();

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

                for idx in 1..num_cells + 1 {
                    addrs.push(self.stack[stack_loc!(AndFrame, e, idx)]);
                }

                let chunk = str_loc_as_cell!(self.heap.len());

                self.heap.push(atom_as_cell!(atom!("cont_chunk"), 1 + num_cells));
                self.heap.push(p_functor);
                self.heap.extend(addrs);

                unify!(self, self.registers[3], chunk);
            }
            &SystemClauseType::GetLiftedHeapFromOffsetDiff => {
                let lh_offset = self.registers[1];
                let lh_offset = cell_as_fixnum!(self.store(self.deref(lh_offset))).get_num() as usize;

                if lh_offset >= self.lifted_heap.len() {
                    let solutions = self.registers[2];
                    let diff = self.registers[3];

                    unify_fn!(self, solutions, diff);
                } else {
                    let h = self.heap.len();
                    let mut last_index = h;

                    for value in self.lifted_heap[lh_offset ..].iter().cloned() {
                        last_index = self.heap.len();
                        self.heap.push(value + h);
                    }

                    if last_index < self.heap.len() {
                        let diff = self.registers[3];
                        unify_fn!(self, diff, self.heap[last_index]);
                    }

                    self.lifted_heap.truncate(lh_offset);

                    let solutions = self.registers[2];
                    unify_fn!(self, heap_loc_as_cell!(h), solutions);
                }
            }
            &SystemClauseType::GetLiftedHeapFromOffset => {
                let lh_offset = self.registers[1];
                let lh_offset = cell_as_fixnum!(self.store(self.deref(lh_offset))).get_num() as usize;

                if lh_offset >= self.lifted_heap.len() {
                    let solutions = self.registers[2];
                    unify_fn!(self, solutions, empty_list_as_cell!());
                } else {
                    let h = self.heap.len();

                    for addr in self.lifted_heap[lh_offset..].iter().cloned() {
                        self.heap.push(addr + h);
                    }

                    self.lifted_heap.truncate(lh_offset);

                    let solutions = self.registers[2];
                    unify_fn!(self, heap_loc_as_cell!(h), solutions);
                }
            }
            &SystemClauseType::GetDoubleQuotes => {
                let a1 = self.store(self.deref(self.registers[1]));

                self.unify_atom(
                    match self.flags.double_quotes {
                        DoubleQuotes::Chars => atom!("chars"),
                        DoubleQuotes::Atom => atom!("atom"),
                        DoubleQuotes::Codes => atom!("codes"),
                    },
                    a1,
                );
            }
            &SystemClauseType::GetSCCCleaner => {
                let dest = self.registers[1];

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
                }

                self.fail = true;
            }
            &SystemClauseType::Halt => {
                let code = self.store(self.deref(self.registers[1]));

                let code = match Number::try_from(code) {
                    Ok(Number::Fixnum(n)) => i32::try_from(n.get_num()).unwrap(),
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
                let addr = self.registers[1];
                let b = self.b;
                let prev_block = self.block;

                if cut_policy.downcast_ref::<SCCCutPolicy>().is_err() {
                    let (r_c_w_h, r_c_wo_h) = indices.get_cleaner_sites();
                    *cut_policy = Box::new(SCCCutPolicy::new(r_c_w_h, r_c_wo_h));
                }

                match cut_policy.downcast_mut::<SCCCutPolicy>().ok() {
                    Some(cut_policy) => {
                        self.install_new_block(self.registers[2]);
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
                let a1 = self.store(self.deref(self.registers[1]));
                let a2 = self.store(self.deref(self.registers[2]));

                if call_policy.downcast_ref::<CWILCallPolicy>().is_err() {
                    CWILCallPolicy::new_in_place(call_policy);
                }

                let n = match Number::try_from(a2) {
                    Ok(Number::Fixnum(bp)) => bp.get_num() as usize,
                    Ok(Number::Integer(n)) => n.to_usize().unwrap(),
                    _ => {
                        let stub = functor_stub(
                            atom!("call_with_inference_limit"),
                            3,
                        );

                        let err = self.type_error(ValidType::Integer, a2);
                        return Err(self.error_form(err, stub));
                    }
                };

                let bp = cell_as_fixnum!(a1).get_num() as usize;

                match call_policy.downcast_mut::<CWILCallPolicy>().ok() {
                    Some(call_policy) => {
                        let count = call_policy.add_limit(n, bp);
                        let count = arena_alloc!(count.clone(), &mut self.arena);

                        let a3 = self.store(self.deref(self.registers[3]));
                        self.unify_big_int(count, a3);
                    }
                    None => {
                        panic!(
                            "install_inference_counter: should have installed \\
                             CWILCallPolicy."
                        )
                    }
                }
            }
            &SystemClauseType::ModuleExists => {
                let module = self.store(self.deref(self.registers[1]));
                let module_name = cell_as_atom!(module);

                self.fail = !indices.modules.contains_key(&module_name);
            }
            &SystemClauseType::NoSuchPredicate => {
                let module_name = cell_as_atom!(self.store(self.deref(self.registers[1])));
                let head = self.store(self.deref(self.registers[2]));

                self.fail = read_heap_cell!(head,
                    (HeapCellValueTag::Str, s) => {
                        let (name, arity) = cell_as_atom_cell!(self.heap[s])
                            .get_name_and_arity();

                        if clause_type_form(name, arity).is_some() {
                            true
                        } else {
                            let index = indices.get_predicate_code_index(
                                name,
                                arity,
                                module_name,
                            )
                            .map(|index| index.get())
                            .unwrap_or(IndexPtr::DynamicUndefined);

                            match index {
                                IndexPtr::DynamicUndefined => false,
                                _ => true,
                            }
                        }
                    }
                    (HeapCellValueTag::Atom, (name, arity)) => {
                        debug_assert_eq!(arity, 0);

                        if clause_type_form(name, 0).is_some() {
                            true
                        } else {
                            let index = indices.get_predicate_code_index(
                                name,
                                0,
                                module_name,
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
                        let err = self.type_error(ValidType::Callable, head);
                        let stub = functor_stub(atom!("clause"), 2);

                        return Err(self.error_form(err, stub));
                    }
                );
            }
            &SystemClauseType::RedoAttrVarBinding => {
                let var = self.store(self.deref(self.registers[1]));
                let value = self.store(self.deref(self.registers[2]));

                debug_assert_eq!(HeapCellValueTag::AttrVar, var.get_tag());
                self.heap[var.get_value()] = value;
            }
            &SystemClauseType::ResetAttrVarState => {
                self.attr_var_init.reset();
            }
            &SystemClauseType::RemoveCallPolicyCheck => {
                let restore_default = match call_policy.downcast_mut::<CWILCallPolicy>().ok() {
                    Some(call_policy) => {
                        let a1 = self.store(self.deref(self.registers[1]));
                        let bp = cell_as_fixnum!(a1).get_num() as usize;

                        if call_policy.is_empty() && bp == self.b {
                            Some(call_policy.into_inner())
                        } else {
                            None
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
                        let a1 = self.store(self.deref(self.registers[1]));
                        let bp = cell_as_fixnum!(a1).get_num() as usize;

                        let count = call_policy.remove_limit(bp).clone();
                        let count = arena_alloc!(count.clone(), &mut self.arena);

                        let a2 = self.store(self.deref(self.registers[2]));

                        self.unify_big_int(count, a2);
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
                    self.registers[i] = self.stack[stack_loc!(AndFrame, e, i)];
                }

                self.b0 = cell_as_fixnum!(self.stack[stack_loc!(AndFrame, e, frame_len - 1)])
                    .get_num() as usize;

                self.num_of_args = cell_as_fixnum!(self.stack[stack_loc!(AndFrame, e, frame_len)])
                    .get_num() as usize;

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
                let addr = self.store(self.deref(self.registers[1]));
                let stream =
                    self.get_stream_or_alias(addr, &indices.stream_aliases, atom!("set_input"), 1)?;

                if !stream.is_input_stream() {
                    let stub = functor_stub(atom!("set_input"), 1);

                    let user_alias = atom_as_cell!(atom!("user"));

                    let err = self.permission_error(
                        Permission::InputStream,
                        atom!("stream"),
                        user_alias,
                    );

                    return Err(self.error_form(err, stub));
                }

                *current_input_stream = stream;
            }
            &SystemClauseType::SetOutput => {
                let addr = self.store(self.deref(self.registers[1]));
                let stream =
                    self.get_stream_or_alias(addr, &indices.stream_aliases, atom!("set_output"), 1)?;

                if !stream.is_output_stream() {
                    let stub = functor_stub(atom!("set_input"), 1);

                    let user_alias = atom_as_cell!(atom!("user"));
                    let err = self.permission_error(
                        Permission::OutputStream,
                        atom!("stream"),
                        user_alias,
                    );

                    return Err(self.error_form(err, stub));
                }

                *current_output_stream = stream;
            }
            &SystemClauseType::SetDoubleQuotes => {
                let atom = cell_as_atom!(self.registers[1]);

                self.flags.double_quotes = match atom {
                    atom!("atom") => DoubleQuotes::Atom,
                    atom!("chars") => DoubleQuotes::Chars,
                    atom!("codes") => DoubleQuotes::Codes,
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                };
            }
            &SystemClauseType::InferenceLevel => {
                let a1 = self.registers[1];
                let a2 = self.store(self.deref(self.registers[2]));

                let bp = cell_as_fixnum!(a2).get_num() as usize;
                let prev_b = self.stack.index_or_frame(self.b).prelude.b;

                if prev_b <= bp {
                    self.unify_atom(atom!("!"), a1)
                } else {
                    self.unify_atom(atom!("true"), a1);
                }
            }
            &SystemClauseType::CleanUpBlock => {
                let nb = self.store(self.deref(self.registers[1]));
                let nb = cell_as_fixnum!(nb).get_num() as usize;

                let b = self.b;

                if nb > 0 && self.stack.index_or_frame(b).prelude.b == nb {
                    self.b = self.stack.index_or_frame(nb).prelude.b;
                }
            }
            &SystemClauseType::EraseBall => {
                self.ball.reset();
            }
            &SystemClauseType::Fail => {
                self.fail = true;
            }
            &SystemClauseType::GetBall => {
                let addr = self.store(self.deref(self.registers[1]));
                let h = self.heap.len();

                if self.ball.stub.len() > 0 {
                    let stub = self.ball.copy_and_align(h);
                    self.heap.extend(stub.into_iter());
                } else {
                    self.fail = true;
                    return Ok(());
                }

                match addr.as_var() {
                    Some(r) => self.bind(r, self.heap[h]),
                    _ => self.fail = true,
                };
            }
            &SystemClauseType::GetCurrentBlock => {
                let n = Fixnum::build_with(i64::try_from(self.block).unwrap());
                self.unify_fixnum(n, self.registers[1]);
            }
            &SystemClauseType::GetBValue => {
                let n = Fixnum::build_with(i64::try_from(self.b).unwrap());
                self.unify_fixnum(n, self.registers[1]);
            }
            &SystemClauseType::GetCutPoint => {
                let n = Fixnum::build_with(i64::try_from(self.b0).unwrap());
                self.unify_fixnum(n, self.registers[1]);
            }
            &SystemClauseType::GetStaggeredCutPoint => {
                use std::sync::Once;

                let b = self.store(self.deref(self.registers[1]));

                static mut SEMICOLON_SECOND_BRANCH_LOC: usize = 0;
                static LOC_INIT: Once = Once::new();

                let semicolon_second_clause_p = unsafe {
                    LOC_INIT.call_once(|| {
                        match indices.code_dir.get(&(atom!(";"), 2)).map(|cell| cell.get()) {
                            Some(IndexPtr::Index(p)) => {
                                match code_repo.code[p] {
                                    Line::Choice(ChoiceInstruction::TryMeElse(o)) => {
                                        SEMICOLON_SECOND_BRANCH_LOC = p + o;
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
                    });

                    LocalCodePtr::DirEntry(SEMICOLON_SECOND_BRANCH_LOC)
                };

                let staggered_b0 = if self.b > 0 {
                    let or_frame = self.stack.index_or_frame(self.b);

                    if or_frame.prelude.bp == semicolon_second_clause_p {
                        or_frame.prelude.b0
                    } else {
                        self.b0
                    }
                } else {
                    self.b0
                };

                let staggered_b0 = integer_as_cell!(
                    Number::arena_from(staggered_b0, &mut self.arena)
                );

                self.bind(b.as_var().unwrap(), staggered_b0);
            }
            &SystemClauseType::InstallNewBlock => {
                self.install_new_block(self.registers[1]);
            }
            &SystemClauseType::NextEP => {
                let first_arg = self.store(self.deref(self.registers[1]));

                read_heap_cell!(first_arg,
                    (HeapCellValueTag::Atom, (name, arity)) => {
                        debug_assert_eq!(name, atom!("first"));
                        debug_assert_eq!(arity, 0);

                        if self.e == 0 {
                            self.fail = true;
                            return Ok(());
                        }

                        let and_frame = self.stack.index_and_frame(self.e);
                        let cp = (and_frame.prelude.cp - 1).unwrap();

                        let e = and_frame.prelude.e;
                        let e = Fixnum::build_with(i64::try_from(e).unwrap());

                        let p = str_loc_as_cell!(self.heap.len());

                        self.heap.extend(cp.as_functor());
                        self.unify_fixnum(e, self.registers[2]);

                        if !self.fail {
                            unify!(self, p, self.registers[3]);
                        }
                    }
                    (HeapCellValueTag::Fixnum, n) => {
                        let e = n.get_num() as usize;

                        if e == 0 {
                            self.fail = true;
                            return Ok(());
                        }

                        // get the call site so that the number of
                        // active permanent variables can be read from
                        // it later.
                        let and_frame = self.stack.index_and_frame(e);
                        let cp = (and_frame.prelude.cp - 1).unwrap();

                        let p = str_loc_as_cell!(self.heap.len());
                        self.heap.extend(cp.as_functor());

                        let e = Fixnum::build_with(i64::try_from(and_frame.prelude.e).unwrap());
                        self.unify_fixnum(e, self.registers[2]);

                        if !self.fail {
                            unify!(self, p, self.registers[3]);
                        }
                    }
                    _ => {
                        unreachable!();
                    }
                );
            }
            &SystemClauseType::PointsToContinuationResetMarker => {
                let addr = self.store(self.deref(self.registers[1]));

                let p = match to_local_code_ptr(&self.heap, addr) {
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
                let addr = self.store(self.deref(self.registers[1]));

                read_heap_cell!(addr,
                    (HeapCellValueTag::Fixnum, n) => {
                        let n = u32::try_from(n.get_num()).ok();
                        let n = n.and_then(std::char::from_u32);

                        self.fail = match n {
                            Some(c) => non_quoted_token(once(c)),
                            None => true,
                        };
                    }
                    (HeapCellValueTag::Char, c) => {
                        self.fail = non_quoted_token(once(c));
                    }
                    (HeapCellValueTag::Atom, (name, arity)) => {
                        debug_assert_eq!(arity, 0);
                        self.fail = non_quoted_token(name.as_str().chars());
                    }
                    _ => {
                        self.fail = true;
                    }
                );
            }
            &SystemClauseType::ReadQueryTerm => {
                current_input_stream.reset();

                set_prompt(true);
                let result = self.read_term(*current_input_stream, indices);
                set_prompt(false);

                match result {
                    Ok(()) => {}
                    Err(e) => {
                        *current_input_stream = input_stream(&mut self.arena);
                        return Err(e);
                    }
                }
            }
            &SystemClauseType::ReadTerm => {
                set_prompt(false);

                let stream = self.get_stream_or_alias(
                    self.registers[1],
                    &indices.stream_aliases,
                    atom!("read_term"),
                    3,
                )?;

                self.read_term(stream, indices)?;
            }
            &SystemClauseType::ReadTermFromChars => {
                if let Some(atom_or_string) = self.value_to_str_like(self.registers[1]) {
                    let chars = atom_or_string.to_string();
                    let stream = Stream::from_owned_string(chars, &mut self.arena);

                    let term_write_result = match self.read(stream, &indices.op_dir) {
                        Ok(term_write_result) => term_write_result,
                        Err(e) => {
                            let stub = functor_stub(atom!("read_term_from_chars"), 2);
                            let e = self.session_error(SessionError::from(e));

                            return Err(self.error_form(e, stub));
                        }
                    };

                    let result = heap_loc_as_cell!(term_write_result.heap_loc);
                    let var = self.store(self.deref(self.registers[2])).as_var().unwrap();

                    self.bind(var, result);
                } else {
                    unreachable!()
                }
            }
            &SystemClauseType::ResetBlock => {
                let addr = self.deref(self.registers[1]);
                self.reset_block(addr);
            }
            &SystemClauseType::ResetContinuationMarker => {
                let h = self.heap.len();

                self.registers[3] = atom_as_cell!(atom!("none"));
                self.registers[4] = heap_loc_as_cell!(h);

                self.heap.push(heap_loc_as_cell!(h));
            }
            &SystemClauseType::SetBall => {
                self.set_ball();
            }
            &SystemClauseType::SetSeed => {
                let seed = self.store(self.deref(self.registers[1]));
                let mut rand = RANDOM_STATE.borrow_mut();

                match Number::try_from(seed) {
                    Ok(Number::Fixnum(n)) => rand.seed(&Integer::from(n)),
                    Ok(Number::Integer(n)) => rand.seed(&*n),
                    Ok(Number::Rational(n)) if n.denom() == &1 => rand.seed(n.numer()),
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                }
            }
            &SystemClauseType::SkipMaxList => {
                if let Err(err) = self.skip_max_list() {
                    return Err(err);
                }
            }
            &SystemClauseType::Sleep => {
                let time = self.store(self.deref(self.registers[1]));

                let time = match Number::try_from(time) {
                    Ok(Number::Float(n)) => n.into_inner(),
                    Ok(Number::Fixnum(n)) => n.get_num() as f64,
                    Ok(Number::Integer(n)) => n.to_f64(),
                    _ => {
                        unreachable!()
                    }
                };

                let duration = Duration::new(1, 0);
                let duration = duration.mul_f64(time);

                std::thread::sleep(duration);
            }
            &SystemClauseType::SocketClientOpen => {
                let addr = self.store(self.deref(self.registers[1]));
                let port = self.store(self.deref(self.registers[2]));

                let socket_atom = cell_as_atom!(addr);

                let _port = read_heap_cell!(port,
                    (HeapCellValueTag::Atom, (name, arity)) => {
                        debug_assert_eq!(arity, 0);
                        name
                    }
                    _ => {
                        self.atom_tbl.build_with(&match Number::try_from(port) {
                            Ok(Number::Fixnum(n)) => n.get_num().to_string(),
                            Ok(Number::Integer(n)) => n.to_string(),
                            _ => {
                                unreachable!()
                            }
                        })
                    }
                );

                let socket_addr = if socket_atom == atom!("") {
                    atom!("127.0.0.1")
                } else {
                    socket_atom
                };

                let alias = self.registers[4];
                let eof_action = self.registers[5];
                let reposition = self.registers[6];
                let stream_type = self.registers[7];

                let options = self.to_stream_options(alias, eof_action, reposition, stream_type);

                if options.reposition() {
                    return Err(self.reposition_error(atom!("socket_client_open"), 3));
                }

                if let Some(alias) = options.get_alias() {
                    if indices.stream_aliases.contains_key(&alias) {
                        return Err(self.occupied_alias_permission_error(
                            alias,
                            atom!("socket_client_open"),
                            3,
                        ));
                    }
                }

                let stream = match TcpStream::connect(socket_addr.as_str()).map_err(|e| e.kind()) {
                    Ok(tcp_stream) => {
                        let mut stream = Stream::from_tcp_stream(socket_addr, tcp_stream, &mut self.arena);

                        *stream.options_mut() = options;

                        if let Some(alias) = stream.options().get_alias() {
                            indices.stream_aliases.insert(alias, stream);
                        }

                        indices.streams.insert(stream);

                        stream_as_cell!(stream)
                    }
                    Err(ErrorKind::PermissionDenied) => {
                        return Err(self.open_permission_error(addr, atom!("socket_client_open"), 3));
                    }
                    Err(ErrorKind::NotFound) => {
                        let stub = functor_stub(atom!("socket_client_open"), 3);
                        let err = self.existence_error(
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

                let stream_addr = self.store(self.deref(self.registers[3]));
                self.bind(stream_addr.as_var().unwrap(), stream);
            }
            &SystemClauseType::SocketServerOpen => {
                let addr = self.store(self.deref(self.registers[1]));
                let socket_atom = cell_as_atom_cell!(addr).get_name();

                let socket_atom = if socket_atom == atom!("[]") {
                    atom!("127.0.0.1")
                } else {
                    socket_atom
                };

                let port = self.store(self.deref(self.registers[2]));

                let port = if port.is_var() {
                    String::from("0")
                } else {
                    match Number::try_from(port) {
                        Ok(Number::Fixnum(n)) => n.get_num().to_string(),
                        Ok(Number::Integer(n)) => n.to_string(),
                        _ => {
                            unreachable!()
                        }
                    }
                };

                let had_zero_port = &port == "0";

                let server_addr = if socket_atom == atom!("") {
                    port
                } else {
                    format!("{}:{}", socket_atom.as_str(), port)
                };

                let (tcp_listener, port) =
                    match TcpListener::bind(server_addr).map_err(|e| e.kind()) {
                        Ok(tcp_listener) => {
                            let port = tcp_listener.local_addr().map(|addr| addr.port()).ok();

                            if let Some(port) = port {
                                (arena_alloc!(tcp_listener, &mut self.arena), port as usize)
                            } else {
                                self.fail = true;
                                return Ok(());
                            }
                        }
                        Err(ErrorKind::PermissionDenied) => {
                            return Err(self.open_permission_error(addr, atom!("socket_server_open"), 2));
                        }
                        _ => {
                            self.fail = true;
                            return Ok(());
                        }
                    };

                let addr = self.store(self.deref(self.registers[3]));
                self.bind(addr.as_var().unwrap(), typed_arena_ptr_as_cell!(tcp_listener));

                if had_zero_port {
                    self.unify_fixnum(Fixnum::build_with(port as i64), self.registers[2]);
                }
            }
            &SystemClauseType::SocketServerAccept => {
                let alias = self.registers[4];
                let eof_action = self.registers[5];
                let reposition = self.registers[6];
                let stream_type = self.registers[7];

                let options = self.to_stream_options(alias, eof_action, reposition, stream_type);

                if options.reposition() {
                    return Err(self.reposition_error(atom!("socket_server_accept"), 4));
                }

                if let Some(alias) = options.get_alias() {
                    if indices.stream_aliases.contains_key(&alias) {
                        return Err(self.occupied_alias_permission_error(
                            alias,
                            atom!("socket_server_accept"),
                            4,
                        ));
                    }
                }

                let culprit = self.store(self.deref(self.registers[1]));

                read_heap_cell!(culprit,
                    (HeapCellValueTag::Cons, cons_ptr) => {
                        match_untyped_arena_ptr!(cons_ptr,
                             (ArenaHeaderTag::TcpListener, tcp_listener) => {
                                 match tcp_listener.accept().ok() {
                                     Some((tcp_stream, socket_addr)) => {
                                         let client = self.atom_tbl.build_with(&socket_addr.to_string());

                                         let mut tcp_stream = Stream::from_tcp_stream(
                                             client,
                                             tcp_stream,
                                             &mut self.arena,
                                         );

                                         *tcp_stream.options_mut() = options;

                                         if let Some(alias) = &tcp_stream.options().get_alias() {
                                             indices.stream_aliases.insert(*alias, tcp_stream);
                                         }

                                         indices.streams.insert(tcp_stream);

                                         let tcp_stream = stream_as_cell!(tcp_stream);
                                         let client = atom_as_cell!(client);

                                         let client_addr = self.store(self.deref(self.registers[2]));
                                         let stream_addr = self.store(self.deref(self.registers[3]));

                                         self.bind(client_addr.as_var().unwrap(), client);
                                         self.bind(stream_addr.as_var().unwrap(), tcp_stream);

                                         return return_from_clause!(self.last_call, self);
                                     }
                                     None => {
                                         self.fail = true;
                                         return Ok(());
                                     }
                                 }
                             }
                             _ => {
                             }
                        );
                    }
                    _ => {
                    }
                );
            }
            &SystemClauseType::TLSClientConnect => {
                if let Some(hostname) = self.value_to_str_like(self.registers[1]) {
                    let stream0 = self.get_stream_or_alias(
                        self.registers[2],
                        &indices.stream_aliases,
                        atom!("tls_client_negotiate"),
                        3,
                    )?;

                    let connector = TlsConnector::new().unwrap();
                    let stream =
                        match connector.connect(hostname.as_str(), stream0) {
                            Ok(tls_stream) => tls_stream,
                            Err(_) => {
                                return Err(self.open_permission_error(
                                    self[temp_v!(1)],
                                    atom!("tls_client_negotiate"),
                                    3,
                                ));
                            }
                        };

                    let addr = atom!("TLS");
                    let stream = Stream::from_tls_stream(addr, stream, &mut self.arena);
                    indices.streams.insert(stream);

                    self.heap.push(stream_as_cell!(stream));
                    let stream_addr = self.store(self.deref(self.registers[3]));
                    self.bind(stream_addr.as_var().unwrap(), stream_as_cell!(stream));
                } else {
                    unreachable!();
                }
            }
            &SystemClauseType::TLSAcceptClient => {
                let pkcs12 = self.string_encoding_bytes(self.registers[1], atom!("octet"));

                if let Some(password) = self.value_to_str_like(self.registers[2]) {
                    let identity =
                        match Identity::from_pkcs12(&pkcs12, password.as_str()) {
                            Ok(identity) => identity,
                            Err(_) => {
                                return Err(self.open_permission_error(
                                    self.registers[1],
                                    atom!("tls_server_negotiate"),
                                    3,
                                ));
                            }
                        };

                    let stream0 = self.get_stream_or_alias(
                        self.registers[3],
                        &indices.stream_aliases,
                        atom!("tls_server_negotiate"),
                        3,
                    )?;

                    let acceptor = TlsAcceptor::new(identity).unwrap();

                    let stream =
                        match acceptor.accept(stream0) {
                            Ok(tls_stream) => tls_stream,
                            Err(_) => {
                                return Err(self.open_permission_error(
                                    self.registers[3],
                                    atom!("tls_server_negotiate"),
                                    3,
                                ));
                            }
                        };

                    let stream = Stream::from_tls_stream(atom!("TLS"), stream, &mut self.arena);
                    indices.streams.insert(stream);

                    let stream_addr = self.store(self.deref(self.registers[4]));
                    self.bind(stream_addr.as_var().unwrap(), stream_as_cell!(stream));
                } else {
                    unreachable!();
                }
            }
            &SystemClauseType::SocketServerClose => {
                let culprit = self.store(self.deref(self.registers[1]));

                read_heap_cell!(culprit,
                    (HeapCellValueTag::Cons, cons_ptr) => {
                        match_untyped_arena_ptr!(cons_ptr,
                            (ArenaHeaderTag::TcpListener, tcp_listener) => {
                                unsafe {
                                    // dropping closes the instance.
                                    std::ptr::drop_in_place(&mut tcp_listener as *mut _);
                                }

                                tcp_listener.set_tag(ArenaHeaderTag::Dropped);
                                return return_from_clause!(self.last_call, self);
                            }
                            _ => {
                            }
                        );
                    }
                    _ => {
                    }
                );

                let err = self.type_error(ValidType::TcpListener, culprit);
                let stub = functor_stub(atom!("socket_server_close"), 1);

                return Err(self.error_form(err, stub));
            }
            &SystemClauseType::SetStreamPosition => {
                let mut stream = self.get_stream_or_alias(
                    self.registers[1],
                    &indices.stream_aliases,
                    atom!("set_stream_position"),
                    2,
                )?;

                if !stream.options().reposition() {
                    let stub = functor_stub(atom!("set_stream_position"), 2);

                    let err = self.permission_error(
                        Permission::Reposition,
                        atom!("stream"),
                        vec![stream_as_cell!(stream)],
                    );

                    return Err(self.error_form(err, stub));
                }

                let position = self.store(self.deref(self.registers[2]));

                let position = match Number::try_from(position) {
                    Ok(Number::Fixnum(n)) => n.get_num() as u64,
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
                    self.registers[1],
                    &indices.stream_aliases,
                    atom!("stream_property"),
                    2,
                )?;

                let atom = cell_as_atom!(self.store(self.deref(self.registers[2])));

                let property = match atom {
                    atom!("file_name") => {
                        atom_as_cell!(if let Some(file_name) = stream.file_name() {
                            file_name
                        } else {
                            self.fail = true;
                            return Ok(());
                        })
                    }
                    atom!("mode") => atom_as_cell!(stream.mode()),
                    atom!("direction") =>
                        atom_as_cell!(if stream.is_input_stream() && stream.is_output_stream() {
                            atom!("input_output")
                        } else if stream.is_input_stream() {
                            atom!("input")
                        } else {
                            atom!("output")
                        }),
                    atom!("alias") => {
                        atom_as_cell!(if let Some(alias) = stream.options().get_alias() {
                            alias
                        } else {
                            self.fail = true;
                            return Ok(());
                        })
                    }
                    atom!("position") => {
                        if let Some((position, lines_read)) = stream.position() {
                            let h = self.heap.len();

                            let position_term = functor!(
                                atom!("position_and_lines_read"),
                                [integer(position, &mut self.arena),
                                 integer(lines_read, &mut self.arena)]
                            );

                            self.heap.extend(position_term.into_iter());
                            str_loc_as_cell!(h)
                        } else {
                            self.fail = true;
                            return Ok(());
                        }
                    }
                    atom!("end_of_stream") => {
                        let end_of_stream_pos = stream.position_relative_to_end();
                        atom_as_cell!(end_of_stream_pos.as_atom())
                    }
                    atom!("eof_action") => {
                        atom_as_cell!(stream.options().eof_action().as_atom())
                    }
                    atom!("reposition") =>
                        atom_as_cell!(if stream.options().reposition() {
                            atom!("true")
                        } else {
                            atom!("false")
                        }),
                    atom!("type") => {
                        atom_as_cell!(stream.options().stream_type().as_property_atom())
                    }
                    _ => {
                        unreachable!()
                    }
                };

                unify!(self, property, self.registers[3]);
            }
            &SystemClauseType::StoreGlobalVar => {
                let key = cell_as_atom!(self.store(self.deref(self.registers[1])));

                let value = self.registers[2];
                let mut ball = Ball::new();

                ball.boundary = self.heap.len();

                copy_term(
                    CopyBallTerm::new(&mut self.stack, &mut self.heap, &mut ball.stub),
                    value,
                    AttrVarPolicy::DeepCopy,
                );

                indices.global_variables.insert(key, (ball, None));
            }
            &SystemClauseType::StoreBacktrackableGlobalVar => {
                let key = cell_as_atom!(self.store(self.deref(self.registers[1])));
                let new_value = self.store(self.deref(self.registers[2]));

                match indices.global_variables.get_mut(&key) {
                    Some((_, ref mut loc)) => match loc {
                        Some(ref mut value) => {
                            self.trail(TrailRef::BlackboardOffset(key, *value));
                            *value = new_value;
                        }
                        loc @ None => {
                            self.trail(TrailRef::BlackboardEntry(key));
                            *loc = Some(new_value);
                        }
                    },
                    None => {
                        self.trail(TrailRef::BlackboardEntry(key));
                        indices
                            .global_variables
                            .insert(key, (Ball::new(), Some(new_value)));
                    }
                }
            }
            &SystemClauseType::TermAttributedVariables => {
                if self.registers[1].is_constant() {
                    self.unify_atom(atom!("[]"), self.store(self.deref(self.registers[2])));
                    return return_from_clause!(self.last_call, self);
                }

                let seen_vars = self.attr_vars_of_term(self.registers[1]);
                let outcome = heap_loc_as_cell!(
                    iter_to_heap_list(&mut self.heap, seen_vars.into_iter())
                );

                unify_fn!(self, self.registers[2], outcome);
            }
            &SystemClauseType::Succeed => {}
            &SystemClauseType::TermVariables => {
                let a1 = self.registers[1];
                let a2 = self.registers[2];

                let stored_v = self.store(self.deref(a1));

                if stored_v.is_constant() {
                    self.unify_atom(atom!("[]"), self.store(self.deref(a2)));
                    return return_from_clause!(self.last_call, self);
                }

                let mut seen_set = IndexSet::new();

                {
                    let mut iter = stackless_preorder_iter(&mut self.heap, stored_v);

                    while let Some(addr) = iter.next() {
                        let addr = unmark_cell_bits!(addr);

                        if addr.is_var() {
                            seen_set.insert(addr);
                        }
                    }
                }

                let outcome = heap_loc_as_cell!(
                    filtered_iter_to_heap_list(
                        &mut self.heap,
                        seen_set.into_iter().rev(),
                        |heap, value| {
                            heap_bound_store(
                                heap,
                                heap_bound_deref(heap, value),
                            ).is_var()
                        },
                    )
                );

                unify_fn!(self, a2, outcome);
            }
            &SystemClauseType::TermVariablesUnderMaxDepth => {
		        // Term, MaxDepth, VarList
		        let max_depth = cell_as_fixnum!(
		            self.store(self.deref(self.registers[2]))
		        ).get_num() as usize;

		        self.term_variables_under_max_depth(self.registers[1], max_depth, self.registers[3]);
            }
            &SystemClauseType::TruncateLiftedHeapTo => {
                let a1 = self.store(self.deref(self.registers[1]));
                let lh_offset = cell_as_fixnum!(a1).get_num() as usize;

                self.lifted_heap.truncate(lh_offset);
            }
            &SystemClauseType::UnifyWithOccursCheck => {
                let a1 = self.registers[1];
                let a2 = self.registers[2];

                unify_with_occurs_check!(self, a1, a2);
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

                    let and_frame = self.stack.index_and_frame(e);

                    cp = and_frame.prelude.cp;
                    e = and_frame.prelude.e;
                }
            }
            &SystemClauseType::UnwindStack => {
                self.unwind_stack();
            }
            /*
            &SystemClauseType::Variant => {
                self.fail = self.structural_eq_test();
            }
            */
            &SystemClauseType::WAMInstructions => {
                let module_name = cell_as_atom!(self.store(self.deref(self.registers[1])));

                let name = self.registers[2];
                let arity = self.registers[3];

                let name = cell_as_atom!(self.store(self.deref(name)));
                let arity = self.store(self.deref(arity));

                let arity = match Number::try_from(arity) {
                    Ok(Number::Fixnum(n)) => n.get_num() as usize,
                    Ok(Number::Integer(n)) => n.to_usize().unwrap(),
                    _ => {
                        unreachable!()
                    }
                };

                let key = (name, arity);

                let first_idx = match module_name {
                    atom!("user") => indices.code_dir.get(&key),
                    _ => match indices.modules.get(&module_name) {
                        Some(module) => module.code_dir.get(&key),
                        None => {
                            let stub = functor_stub(key.0, key.1);
                            let err = self.session_error(
                                SessionError::from(CompilationError::InvalidModuleResolution(
                                    module_name,
                                )),
                            );

                            return Err(self.error_form(err, stub));
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
                        let stub = functor_stub(name, arity);
                        let err = self.existence_error(
                            ExistenceError::Procedure(name, arity),
                        );

                        return Err(self.error_form(err, stub));
                    }
                };

                let mut h = self.heap.len();

                let mut functors = vec![];
                let mut functor_list = vec![];

                walk_code(&code_repo.code, first_idx, |instr| {
                    let old_len = functors.len();
                    instr.enqueue_functors(h, &mut self.arena, &mut functors);
                    let new_len = functors.len();

                    for index in old_len..new_len {
                        let functor_len = functors[index].len();

                        match functor_len {
                            0 => {}
                            1 => {
                                functor_list.push(heap_loc_as_cell!(h));
                                h += functor_len;
                            }
                            _ => {
                                functor_list.push(str_loc_as_cell!(h));
                                h += functor_len;
                            }
                        }
                    }
                });

                for functor in functors {
                    self.heap.extend(functor.into_iter());
                }

                let listing = heap_loc_as_cell!(
                    iter_to_heap_list(&mut self.heap, functor_list.into_iter())
                );

                let listing_var = self.registers[4];

                unify!(self, listing, listing_var);
            }
            &SystemClauseType::WriteTerm => {
                let mut stream = self.get_stream_or_alias(
                    self.registers[1],
                    &indices.stream_aliases,
                    atom!("write_term"),
                    3,
                )?;

                self.check_stream_properties(
                    stream,
                    StreamType::Text,
                    None, // input
                    atom!("write_term"),
                    3,
                )?;

                let opt_err = if !stream.is_output_stream() {
                    Some(atom!("stream")) // 8.14.2.3 g)
                } else if stream.options().stream_type() == StreamType::Binary {
                    Some(atom!("binary_stream")) // 8.14.2.3 h)
                } else {
                    None
                };

                if let Some(err_atom) = opt_err {
                    return Err(self.stream_permission_error(
                        Permission::OutputStream,
                        err_atom,
                        stream,
                        atom!("write_term"),
                        3,
                    ));
                }

                let printer = match self.write_term(&indices.op_dir)? {
                    Some(printer) => printer,
                    None => {
                        // this next line is executed by
                        // MachineState::write_term in this case. it's
                        // commented here because rustc can't prove
                        // that it's no longer borrowed.

                        // self.fail = true;
                        return Ok(());
                    }
                };

                let output = printer.print();

                match write!(&mut stream, "{}", output.result()) {
                    Ok(_) => {}
                    Err(_) => {
                        let stub = functor_stub(atom!("open"), 4);
                        let err = self.existence_error(
                            ExistenceError::Stream(self.registers[1]),
                        );

                        return Err(self.error_form(err, stub));
                    }
                }

                stream.flush().unwrap();
            }
            &SystemClauseType::WriteTermToChars => {
                let printer = match self.write_term(&indices.op_dir)? {
                    None => {
                        // this next line is executed by
                        // MachineState::write_term in this case. it's
                        // commented here because rustc can't prove
                        // that it's no longer borrowed.

                        // self.fail = true;
                        return Ok(());
                    }
                    Some(printer) => printer,
                };

                let result = printer.print().result();
                let chars = put_complete_string(&mut self.heap, &result, &mut self.atom_tbl);

                let result_addr = self.store(self.deref(self.registers[1]));

                if let Some(var) = result_addr.as_var() {
                    self.bind(var, chars);
                } else {
                    unreachable!()
                }
            }
            &SystemClauseType::ScryerPrologVersion => {
                use git_version::git_version;

                let buffer = git_version!(cargo_prefix = "cargo:", fallback = "unknown");
                let buffer_atom = self.atom_tbl.build_with(buffer);

                self.unify_complete_string(buffer_atom, self.store(self.deref(self.registers[1])));
            }
            &SystemClauseType::CryptoRandomByte => {
                let arg = self.registers[1];
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

                let byte = Fixnum::build_with(bytes[0] as i64);
                self.unify_fixnum(byte, arg);
            }
            &SystemClauseType::CryptoDataHash => {
                let encoding = cell_as_atom!(self.registers[2]);
                let bytes = self.string_encoding_bytes(self.registers[1], encoding);

                let algorithm = cell_as_atom!(self.registers[4]);

                let ints_list = match algorithm {
                    atom!("sha3_224") => {
                        let mut context = Sha3_224::new();
                        context.input(&bytes);

                        heap_loc_as_cell!(
                            iter_to_heap_list(
                                &mut self.heap,
                                context
                                    .result()
                                    .as_ref()
                                    .iter()
                                    .map(|b| fixnum_as_cell!(Fixnum::build_with(*b as i64))),
                            )
                        )
                    }
                    atom!("sha3_256") => {
                        let mut context = Sha3_256::new();
                        context.input(&bytes);
                        heap_loc_as_cell!(
                            iter_to_heap_list(
                                &mut self.heap,
                                context
                                    .result()
                                    .as_ref()
                                    .iter()
                                    .map(|b| fixnum_as_cell!(Fixnum::build_with(*b as i64))),
                            )
                        )
                    }
                    atom!("sha3_384") => {
                        let mut context = Sha3_384::new();
                        context.input(&bytes);

                        heap_loc_as_cell!(
                            iter_to_heap_list(
                                &mut self.heap,
                                context
                                    .result()
                                    .as_ref()
                                    .iter()
                                    .map(|b| fixnum_as_cell!(Fixnum::build_with(*b as i64))),
                            )
                        )
                    }
                    atom!("sha3_512") => {
                        let mut context = Sha3_512::new();
                        context.input(&bytes);

                        heap_loc_as_cell!(
                            iter_to_heap_list(
                                &mut self.heap,
                                context
                                    .result()
                                    .as_ref()
                                    .iter()
                                    .map(|b| fixnum_as_cell!(Fixnum::build_with(*b as i64))),
                            )
                        )
                    }
                    atom!("blake2s256") => {
                        let mut context = Blake2s::new();
                        context.input(&bytes);

                        heap_loc_as_cell!(
                            iter_to_heap_list(
                                &mut self.heap,
                                context
                                    .result()
                                    .as_ref()
                                    .iter()
                                    .map(|b| fixnum_as_cell!(Fixnum::build_with(*b as i64))),
                            )
                        )
                    }
                    atom!("blake2b512") => {
                        let mut context = Blake2b::new();
                        context.input(&bytes);

                        heap_loc_as_cell!(
                            iter_to_heap_list(
                                &mut self.heap,
                                context
                                    .result()
                                    .as_ref()
                                    .iter()
                                    .map(|b| fixnum_as_cell!(Fixnum::build_with(*b as i64))),
                            )
                        )
                    }
                    atom!("ripemd160") => {
                        let mut context = Ripemd160::new();
                        context.input(&bytes);

                        heap_loc_as_cell!(
                            iter_to_heap_list(
                                &mut self.heap,
                                context
                                    .result()
                                    .as_ref()
                                    .iter()
                                    .map(|b| fixnum_as_cell!(Fixnum::build_with(*b as i64))),
                            )
                        )
                    }
                    _ => {
                        let ints = digest::digest(
                            match algorithm {
                                atom!("sha256") => &digest::SHA256,
                                atom!("sha384") => &digest::SHA384,
                                atom!("sha512") => &digest::SHA512,
                                atom!("sha512_256") => &digest::SHA512_256,
                                _ => {
                                    unreachable!()
                                }
                            },
                            &bytes,
                        );

                        heap_loc_as_cell!(
                            iter_to_heap_list(
                                &mut self.heap,
                                ints.as_ref()
                                    .iter()
                                    .map(|b| fixnum_as_cell!(Fixnum::build_with(*b as i64))),
                            )
                        )
                    }
                };

                unify!(self, self.registers[3], ints_list);
            }
            &SystemClauseType::CryptoDataHKDF => {
                let encoding = cell_as_atom!(self.registers[2]);
                let data = self.string_encoding_bytes(self.registers[1], encoding);

                let stub1_gen = || functor_stub(atom!("crypto_data_hkdf"), 4);
                let salt = self.integers_to_bytevec(self.registers[3], stub1_gen);

                let stub2_gen = || functor_stub(atom!("crypto_data_hkdf"), 4);
                let info = self.integers_to_bytevec(self.registers[4], stub2_gen);

                let algorithm = cell_as_atom!(self.registers[5]);

                let length = self.store(self.deref(self.registers[6]));

                let length = match Number::try_from(length) {
                    Ok(Number::Fixnum(n)) => usize::try_from(n.get_num()).unwrap(),
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
                    let digest_alg = match algorithm {
                        atom!("sha256") => hkdf::HKDF_SHA256,
                        atom!("sha384") => hkdf::HKDF_SHA384,
                        atom!("sha512") => hkdf::HKDF_SHA512,
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

                    heap_loc_as_cell!(
                        iter_to_heap_list(
                            &mut self.heap,
                            bytes
                                .iter()
                                .map(|b| fixnum_as_cell!(Fixnum::build_with(*b as i64))),
                        )
                    )
                };

                unify!(self, self.registers[7], ints_list);
            }
            &SystemClauseType::CryptoPasswordHash => {
                let stub1_gen = || functor_stub(atom!("crypto_password_hash"), 3);
                let data = self.integers_to_bytevec(self.registers[1], stub1_gen);
                let stub2_gen = || functor_stub(atom!("crypto_password_hash"), 3);
                let salt = self.integers_to_bytevec(self.registers[2], stub2_gen);

                let iterations = self.store(self.deref(self.registers[3]));

                let iterations = match Number::try_from(iterations) {
                    Ok(Number::Fixnum(n)) => u64::try_from(n.get_num()).unwrap(),
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

                    heap_loc_as_cell!(
                        iter_to_heap_list(
                            &mut self.heap,
                            bytes
                                .iter()
                                .map(|b| fixnum_as_cell!(Fixnum::build_with(*b as i64))),
                        )
                    )
                };

                unify!(self, self.registers[4], ints_list);
            }
            &SystemClauseType::CryptoDataEncrypt => {
                let encoding = cell_as_atom!(self.registers[3]);

                let data = self.string_encoding_bytes(self.registers[1], encoding);
                let aad = self.string_encoding_bytes(self.registers[2], encoding);

                let stub2_gen = || functor_stub(atom!("crypto_data_encrypt"), 7);
                let key = self.integers_to_bytevec(self.registers[4], stub2_gen);

                let stub3_gen = || functor_stub(atom!("crypto_data_encrypt"), 7);
                let iv = self.integers_to_bytevec(self.registers[5], stub3_gen);

                let unbound_key = aead::UnboundKey::new(&aead::CHACHA20_POLY1305, &key).unwrap();
                let nonce = aead::Nonce::try_assume_unique_for_key(&iv).unwrap();
                let key = aead::LessSafeKey::new(unbound_key);

                let mut in_out = data;

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

                let tag_list = heap_loc_as_cell!(
                    iter_to_heap_list(
                        &mut self.heap,
                        tag.as_ref()
                            .iter()
                            .map(|b| fixnum_as_cell!(Fixnum::build_with(*b as i64))),
                    )
                );

                let complete_string = {
                    let buffer = String::from_iter(in_out.iter().map(|b| *b as char));
                    put_complete_string(&mut self.heap, &buffer, &mut self.atom_tbl)
                };

                unify!(self, self.registers[6], tag_list);
                unify!(self, self.registers[7], complete_string);
            }
            &SystemClauseType::CryptoDataDecrypt => {
                let data = self.string_encoding_bytes(self.registers[1], atom!("octet"));
                let encoding = cell_as_atom!(self.registers[5]);

                let aad = self.string_encoding_bytes(self.registers[2], encoding);
                let stub1_gen = || functor_stub(atom!("crypto_data_decrypt"), 7);

                let key = self.integers_to_bytevec(self.registers[3], stub1_gen);
                let stub2_gen = || functor_stub(atom!("crypto_data_decrypt"), 7);
                let iv = self.integers_to_bytevec(self.registers[4], stub2_gen);

                let unbound_key = aead::UnboundKey::new(&aead::CHACHA20_POLY1305, &key).unwrap();
                let nonce = aead::Nonce::try_assume_unique_for_key(&iv).unwrap();
                let key = aead::LessSafeKey::new(unbound_key);

                let mut in_out = data;

                let complete_string = {
                    let decrypted_data =
                        match key.open_in_place(nonce, aead::Aad::from(aad), &mut in_out) {
                            Ok(d) => d,
                            _ => {
                                self.fail = true;
                                return Ok(());
                            }
                        };

                    let buffer = match encoding {
                        atom!("octet") => String::from_iter(decrypted_data.iter().map(|b| *b as char)),
                        atom!("utf8") => match String::from_utf8(decrypted_data.to_vec()) {
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

                    put_complete_string(&mut self.heap, &buffer, &mut self.atom_tbl)
                };

                unify!(self, self.registers[6], complete_string);
            }
            &SystemClauseType::CryptoCurveScalarMult => {
                let curve = cell_as_atom!(self.registers[1]);

                let curve_id = match curve {
                    atom!("secp112r1") => Nid::SECP112R1,
                    atom!("secp256k1") => Nid::SECP256K1,
                    _ => {
                        unreachable!()
                    }
                };

                let scalar = self.store(self.deref(self.registers[2]));

                let scalar = match Number::try_from(scalar) {
                    Ok(Number::Fixnum(n)) => Integer::from(n.get_num()),
                    Ok(Number::Integer(n)) => Integer::from(&*n),
                    _ => {
                        unreachable!()
                    }
                };

                let stub_gen = || functor_stub(atom!("crypto_curve_scalar_mult"), 5);
                let qbytes = self.integers_to_bytevec(self.registers[3], stub_gen);

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

                let sx = put_complete_string(
                    &mut self.heap,
                    &rx.to_dec_str().unwrap(),
                    &mut self.atom_tbl,
                );

                let sy = put_complete_string(
                    &mut self.heap,
                    &ry.to_dec_str().unwrap(),
                    &mut self.atom_tbl,
                );

                unify!(self, self.registers[4], sx);
                unify!(self, self.registers[5], sy);
            }
            &SystemClauseType::Ed25519NewKeyPair => {
                let pkcs8_bytes = signature::Ed25519KeyPair::generate_pkcs8(rng()).unwrap();
                let complete_string = {
                    let buffer = String::from_iter(pkcs8_bytes.as_ref().iter().map(|b| *b as char));
                    put_complete_string(
                        &mut self.heap,
                        &buffer,
                        &mut self.atom_tbl,
                    )
                };

                unify!(self, self.registers[1], complete_string)
            }
            &SystemClauseType::Ed25519KeyPairPublicKey => {
                let bytes = self.string_encoding_bytes(self.registers[1], atom!("octet"));

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

                    put_complete_string(
                        &mut self.heap,
                        &buffer,
                        &mut self.atom_tbl,
                    )
                };

                unify!(self, self.registers[2], complete_string);
            }
            &SystemClauseType::Ed25519Sign => {
                let key = self.string_encoding_bytes(self.registers[1], atom!("octet"));
                let encoding = cell_as_atom!(self.registers[3]);
                let data = self.string_encoding_bytes(self.registers[2], encoding);

                let key_pair = match signature::Ed25519KeyPair::from_pkcs8(&key) {
                    Ok(kp) => kp,
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                };

                let sig = key_pair.sign(&data);

                let sig_list = heap_loc_as_cell!(
                    iter_to_heap_list(
                        &mut self.heap,
                        sig.as_ref()
                            .iter()
                            .map(|b| fixnum_as_cell!(Fixnum::build_with(*b as i64))),
                    )
                );

                unify!(self, self.registers[4], sig_list);
            }
            &SystemClauseType::Ed25519Verify => {
                let key = self.string_encoding_bytes(self.registers[1], atom!("octet"));
                let encoding = cell_as_atom!(self.registers[3]);
                let data = self.string_encoding_bytes(self.registers[2], encoding);
                let stub_gen = || functor_stub(atom!("ed25519_verify"), 5);
                let signature = self.integers_to_bytevec(self.registers[4], stub_gen);

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
                let stub1_gen = || functor_stub(atom!("curve25519_scalar_mult"), 3);
                let scalar_bytes = self.integers_to_bytevec(self.registers[1], stub1_gen);
                let scalar = Scalar(<[u8; 32]>::try_from(&scalar_bytes[..]).unwrap());

                let stub2_gen = || functor_stub(atom!("curve25519_scalar_mult"), 3);
                let point_bytes = self.integers_to_bytevec(self.registers[2], stub2_gen);
                let point = GroupElement(<[u8; 32]>::try_from(&point_bytes[..]).unwrap());

                let result = scalarmult(&scalar, &point).unwrap();

                let string = String::from_iter(result[..].iter().map(|b| *b as char));
                let cstr = put_complete_string(&mut self.heap, &string, &mut self.atom_tbl);

                unify!(self, self.registers[3], cstr);
            }
            &SystemClauseType::FirstNonOctet => {
                let addr = self.store(self.deref(self.registers[1]));

                if let Some(string) = self.value_to_str_like(addr) {
                    for c in string.as_str().chars() {
                        if c as u32 > 255 {
                            let non_octet = self.atom_tbl.build_with(&c.to_string());
                            self.unify_atom(non_octet, self.registers[2]);
                            return return_from_clause!(self.last_call, self);
                        }
                    }
                }

                self.fail = true;
                return Ok(());
            }
            &SystemClauseType::LoadHTML => {
                if let Some(string) = self.value_to_str_like(self.registers[1]) {
                    let doc = select::document::Document::from_read(string.as_str().as_bytes())
                        .unwrap();

                    let result = self.html_node_to_term(indices, doc.nth(0).unwrap());
                    unify!(self, self.registers[2], result);
                } else {
                    self.fail = true;
                    return Ok(());
                }
            }
            &SystemClauseType::LoadXML => {
                if let Some(string) = self.value_to_str_like(self.registers[1]) {
                    match roxmltree::Document::parse(string.as_str()) {
                        Ok(doc) => {
                            let result = self.xml_node_to_term(indices, doc.root_element());
                            unify!(self, self.registers[2], result);
                        }
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
            &SystemClauseType::GetEnv => {
                if let Some(key) = self.value_to_str_like(self.registers[1]) {
                    match env::var(key.as_str()) {
                        Ok(value) => {
                            let cstr = put_complete_string(
                                &mut self.heap,
                                &value,
                                &mut self.atom_tbl,
                            );

                            unify!(self, self.registers[2], cstr);
                        }
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
            &SystemClauseType::SetEnv => {
                let key = self.value_to_str_like(self.registers[1]).unwrap();
                let value = self.value_to_str_like(self.registers[2]).unwrap();

                env::set_var(key.as_str(), value.as_str());
            }
            &SystemClauseType::UnsetEnv => {
                let key = self.value_to_str_like(self.registers[1]).unwrap();
                env::remove_var(key.as_str());
            }
            &SystemClauseType::PID => {
                let pid = process::id();

                match fixnum!(Number, pid as i64, &mut self.arena) {
                    Number::Fixnum(pid) => {
                        self.unify_fixnum(pid, self.registers[1]);
                    }
                    Number::Integer(pid) => {
                        self.unify_big_int(pid, self.registers[1]);
                    }
                    _ => {
                        unreachable!();
                    }
                }
            }
            &SystemClauseType::Shell => {
                // shell executes a command in a system shell
                // the code looks for a SHELL env var to do it in a UNIX-style
                // if not found, the code looks for COMSPEC env var to do it in a DOS-style
                // the output is printed directly to stdout
                // the output status code is returned after finishing
                fn command_result(machine: &mut MachineState, command: std::io::Result<process::ExitStatus>) {
                    match command {
                        Ok(status) => {
                            match status.code() {
                                Some(code) => {
                                    let code = integer_as_cell!(Number::arena_from(code, &mut machine.arena));
                                    unify!(machine, code, machine.registers[2]);
                                }
                                _ => {
                                    machine.fail = true;
                                }
                            }
                        }
                        _ => {
                            machine.fail = true;
                        }
                    }
                }

                let command = self.value_to_str_like(self.store(self.deref(self.registers[1]))).unwrap();

                match env::var("SHELL") {
                    Ok(value) => {
                        let command = process::Command::new(&value)
                            .arg("-c")
                            .arg(command.as_str())
                            .status();
                        command_result(self, command);
                    }
                    _ => {
                        match env::var("COMSPEC") {
                            Ok(value) => {
                                let command = process::Command::new(&value)
                                    .arg("/C")
                                    .arg(command.as_str())
                                    .status();
                                command_result(self, command);
                            }
                            _ => {
                                self.fail = true;
                            }
                        }
                    }
                };
            }
            &SystemClauseType::CharsBase64 => {
                let padding = cell_as_atom!(self.registers[3]);
                let charset = cell_as_atom!(self.registers[4]);

                let config = if padding == atom!("true") {
                    if charset == atom!("standard") {
                        base64::STANDARD
                    } else {
                        base64::URL_SAFE
                    }
                } else {
                    if charset == atom!("standard") {
                        base64::STANDARD_NO_PAD
                    } else {
                        base64::URL_SAFE_NO_PAD
                    }
                };

                if self.store(self.deref(self.registers[1])).is_var() {
                    let b64 = self.value_to_str_like(self.registers[2]).unwrap();
                    let bytes = base64::decode_config(b64.as_str(), config);

                    match bytes {
                        Ok(bs) => {
                            let string = String::from_iter(bs.iter().map(|b| *b as char));
                            let cstr = put_complete_string(
                                &mut self.heap,
                                &string,
                                &mut self.atom_tbl,
                            );

                            unify!(self, self.registers[1], cstr);
                        }
                        _ => {
                            self.fail = true;
                            return Ok(());
                        }
                    }
                } else {
                    let mut bytes = vec![];
                    for c in self.value_to_str_like(self.registers[1]).unwrap().as_str().chars() {
                        if c as u32 > 255 {
                            let stub = functor_stub(atom!("chars_base64"), 3);

                            let err = self.type_error(
                                ValidType::Byte,
                                char_as_cell!(c),
                            );

                            return Err(self.error_form(err, stub));
                        }

                        bytes.push(c as u8);
                    }

                    let b64 = base64::encode_config(bytes, config);
                    let cstr = put_complete_string(
                        &mut self.heap,
                        &b64,
                        &mut self.atom_tbl,
                    );

                    unify!(self, self.registers[2], cstr);
                }
            }
            &SystemClauseType::LoadLibraryAsStream => {
                let library_name = cell_as_atom!(self.store(self.deref(self.registers[1])));

                use crate::machine::LIBRARIES;

                match LIBRARIES.borrow().get(library_name.as_str()) {
                    Some(library) => {
                        let lib_stream = Stream::from_static_string(library, &mut self.arena);
                        unify!(self, stream_as_cell!(lib_stream), self.registers[2]);

                        let mut path_buf = machine::current_dir();

                        path_buf.push("/lib");
                        path_buf.push(library_name.as_str());

                        let library_path_str = path_buf.to_str().unwrap();
                        let library_path = self.atom_tbl.build_with(library_path_str);

                        self.unify_atom(library_path, self.registers[3]);
                    }
                    None => {
                        let stub = functor_stub(atom!("load"), 1);
                        let err = self.existence_error(
                            ExistenceError::ModuleSource(ModuleSource::Library(library_name))
                        );

                        return Err(self.error_form(err, stub));
                    }
                }
            }
            &SystemClauseType::DevourWhitespace => {
                let stream = self.get_stream_or_alias(
                    self.registers[1],
                    &indices.stream_aliases,
                    atom!("$devour_whitespace"),
                    1,
                )?;

                match self.devour_whitespace(stream) {
                    Ok(false) => { // not at EOF.
                    }
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                }
            }
            &SystemClauseType::IsSTOEnabled => {
                if self.unify_fn as usize == MachineState::unify_with_occurs_check as usize {
                    self.unify_atom(atom!("true"), self.registers[1]);
                } else if self.unify_fn as usize
                    == MachineState::unify_with_occurs_check_with_error as usize
                {
                    self.unify_atom(atom!("error"), self.registers[1]);
                } else {
                    self.unify_atom(atom!("false"), self.registers[1]);
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
                        let path_string = put_complete_string(
                            &mut self.heap,
                            path,
                            &mut self.atom_tbl,
                        );

                        unify!(self, self.registers[1], path_string);
                        return return_from_clause!(self.last_call, self);
                    }
                }

                self.fail = true;
            }
            &SystemClauseType::DebugHook => {
                self.fail = false;
            }
            &SystemClauseType::PopCount => {
                let number = self.store(self.deref(self.registers[1]));
                let pop_count = integer_as_cell!(match Number::try_from(number) {
                    Ok(Number::Fixnum(n)) => {
                        Number::Fixnum(Fixnum::build_with(n.get_num().count_ones() as i64))
                    }
                    Ok(Number::Integer(n)) => {
                        Number::arena_from(n.count_ones().unwrap(), &mut self.arena)
                    }
                    _ => {
                        unreachable!()
                    }
                });

                unify!(self, self.registers[2], pop_count);
            }
        };

        return_from_clause!(self.last_call, self)
    }

    pub(super) fn systemtime_to_timestamp(&mut self, system_time: SystemTime) -> Atom {
        let datetime: DateTime<Local> = system_time.into();

        let mut fstr = "[".to_string();
        const SPECIFIERS: [&'static str; 19] = [
            "Y", "m", "d", "H", "M", "S", "y", "b", "B", "a", "A", "w", "u", "U", "W", "j", "D",
            "x", "v",
        ];

        for spec in SPECIFIERS {
            fstr.push_str(&format!("'{}'=\"%{}\", ", spec, spec).to_string());
        }

        fstr.push_str("finis].");
        let s = datetime.format(&fstr).to_string();

        self.atom_tbl.build_with(&s)
    }

    pub(super) fn string_encoding_bytes(&mut self, data_arg: HeapCellValue, encoding: Atom) -> Vec<u8> {
        let data = self.value_to_str_like(data_arg).unwrap();

        match encoding {
            atom!("utf8") => data.as_str().bytes().collect(),
            atom!("octet") => data.as_str().chars().map(|c| c as u8).collect(),
            _ => {
                unreachable!()
            }
        }
    }

    pub(super) fn xml_node_to_term(
        &mut self,
        indices: &mut IndexStore,
        node: roxmltree::Node,
    ) -> HeapCellValue {
        if node.is_text() {
            put_complete_string(
                &mut self.heap,
                node.text().unwrap(),
                &mut self.atom_tbl,
            )
        } else {
            let mut avec = Vec::new();

            for attr in node.attributes() {
                let name = self.atom_tbl.build_with(attr.name());
                let value = put_complete_string(
                    &mut self.heap,
                    &attr.value(),
                    &mut self.atom_tbl,
                );

                avec.push(heap_loc_as_cell!(self.heap.len()));

                self.heap.push(atom_as_cell!(atom!("="), 2));
                self.heap.push(atom_as_cell!(name));
                self.heap.push(value);
            }

            let attrs = heap_loc_as_cell!(
                iter_to_heap_list(&mut self.heap, avec.into_iter())
            );

            let mut cvec = Vec::new();

            for child in node.children() {
                cvec.push(self.xml_node_to_term(indices, child));
            }

            let children = heap_loc_as_cell!(
                iter_to_heap_list(&mut self.heap, cvec.into_iter())
            );

            let tag = self.atom_tbl.build_with(node.tag_name().name());

            let result = heap_loc_as_cell!(self.heap.len());

            self.heap.push(atom_as_cell!(atom!("element"), 3));
            self.heap.push(atom_as_cell!(tag));
            self.heap.push(attrs);
            self.heap.push(children);

            result
        }
    }

    pub(super) fn html_node_to_term(
        &mut self,
        indices: &mut IndexStore,
        node: select::node::Node,
    ) -> HeapCellValue {
        match node.name() {
            None => {
                put_complete_string(
                    &mut self.heap,
                    &node.text(),
                    &mut self.atom_tbl,
                )
            }
            Some(name) => {
                let mut avec = Vec::new();

                for attr in node.attrs() {
                    let name = self.atom_tbl.build_with(attr.0);
                    let value = put_complete_string(
                        &mut self.heap,
                        &attr.1,
                        &mut self.atom_tbl,
                    );

                    avec.push(heap_loc_as_cell!(self.heap.len()));

                    self.heap.push(atom_as_cell!(atom!("="), 2));
                    self.heap.push(atom_as_cell!(name));
                    self.heap.push(value);
                }

                let attrs = heap_loc_as_cell!(
                    iter_to_heap_list(&mut self.heap, avec.into_iter())
                );

                let mut cvec = Vec::new();

                for child in node.children() {
                    cvec.push(self.html_node_to_term(indices, child));
                }

                let children = heap_loc_as_cell!(
                    iter_to_heap_list(&mut self.heap, cvec.into_iter())
                );

                let tag = self.atom_tbl.build_with(name);
                let result = heap_loc_as_cell!(self.heap.len());

                self.heap.push(atom_as_cell!(atom!("element"), 3));
                self.heap.push(atom_as_cell!(tag));
                self.heap.push(attrs);
                self.heap.push(children);

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

