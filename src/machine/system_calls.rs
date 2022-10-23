use crate::parser::ast::*;
use crate::parser::parser::*;

use lazy_static::lazy_static;

use crate::arena::*;
use crate::atom_table::*;
use crate::forms::*;
use crate::heap_iter::*;
use crate::heap_print::*;
use crate::http::{self, HttpListener, HttpResponse};
use crate::instructions::*;
use crate::machine;
use crate::machine::{Machine, VERIFY_ATTR_INTERRUPT_LOC, get_structure_index};
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
use crate::parser::rug::rand::RandState;
use crate::read::*;
use crate::types::*;

use ordered_float::OrderedFloat;

use fxhash::{FxBuildHasher, FxHasher};
use indexmap::IndexSet;

use ref_thread_local::{RefThreadLocal, ref_thread_local};

use std::cell::Cell;
use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::convert::{TryFrom, Infallible};
use std::env;
use std::fs;
use std::hash::{BuildHasher, BuildHasherDefault};
use std::io::{ErrorKind, Read, Write};
use std::iter::{once, FromIterator};
use std::mem;
use std::net::{TcpListener, TcpStream, SocketAddr, ToSocketAddrs};
use std::num::NonZeroU32;
use std::ops::Sub;
use std::process;
use std::rc::Rc;
use std::str::FromStr;
use std::sync::Arc;

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

use crrl::secp256k1;

use sodiumoxide::crypto::scalarmult::curve25519::*;

use native_tls::{TlsConnector,TlsAcceptor,Identity};

use base64;
use roxmltree;
use select;

use hyper::{Body, Server, Client, HeaderMap, Method, Request, Response, Uri};
use hyper::header::{HeaderName, HeaderValue};
use hyper::body::Buf;
use hyper::service::{make_service_fn, service_fn};
use hyper_tls::HttpsConnector;
use tokio::sync::Mutex;
use tokio::sync::mpsc::channel;

ref_thread_local! {
    pub(crate) static managed RANDOM_STATE: RandState<'static> = RandState::new();
}

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
            return Some(CycleSearchResult::Cyclic(self.lam));
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

                return CycleSearchResult::PStrLocation(self.num_steps(), n);
            }
            (HeapCellValueTag::Atom, (name, arity)) => {
                return if name == atom!("[]") && arity == 0 {
                    CycleSearchResult::ProperList(self.num_steps())
                } else {
                    CycleSearchResult::NotList(self.num_steps(), heap[self.hare])
                };
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(heap[s])
                    .get_name_and_arity();

                return if name == atom!("[]") && arity == 0 {
                    CycleSearchResult::ProperList(self.num_steps())
                } else {
                    CycleSearchResult::NotList(self.num_steps(), heap[self.hare])
                };
            }
            (HeapCellValueTag::Lis, l) => {
                return CycleSearchResult::UntouchedList(self.num_steps(), l);
            }
            _ => {
                return CycleSearchResult::NotList(self.num_steps(), heap[self.hare]);
            }
        );
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

    #[inline(always)]
    fn cycle_step(&mut self, heap: &[HeapCellValue]) -> Option<CycleSearchResult> {
        loop {
            let value = heap[self.hare];

            read_heap_cell!(value,
                (HeapCellValueTag::PStrLoc, h) => {
                    return self.add_pstr_chars_and_step(&heap, h);
                }
                (HeapCellValueTag::CStr | HeapCellValueTag::PStrOffset) => {
                    return self.add_pstr_chars_and_step(&heap, self.hare);
                }
                (HeapCellValueTag::Lis, h) => {
                    return self.step(h+1);
                }
                (HeapCellValueTag::Str, s) => {
                    let (name, arity) = cell_as_atom_cell!(heap[s]).get_name_and_arity();

                    return if name == atom!(".") && arity == 2 {
                        self.step(s+2)
                    } else {
                        Some(CycleSearchResult::NotList(self.num_steps(), value))
                    };
                }
                (HeapCellValueTag::Atom, (name, arity)) => {
                    debug_assert!(arity == 0);

                    return if name == atom!("[]") {
                        Some(CycleSearchResult::ProperList(self.num_steps()))
                    } else {
                        Some(CycleSearchResult::NotList(self.num_steps(), value))
                    };
                }
                (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
                    if self.hare == h {
                        let r = value.as_var().unwrap();
                        return Some(CycleSearchResult::PartialList(self.num_steps(), r));
                    }

                    self.hare = h;
                }
                _ => {
                    return Some(CycleSearchResult::NotList(self.num_steps(), value));
                }
            );
        }
    }

    pub fn detect_cycles(heap: &[HeapCellValue], value: HeapCellValue) -> CycleSearchResult {
        let mut pstr_chars = 0;

        let hare = read_heap_cell!(value,
            (HeapCellValueTag::Lis, offset) => {
                offset+1
            }
            (HeapCellValueTag::PStrLoc, h) => {
                let (h_offset, n) = pstr_loc_and_offset(&heap, h);
                let n = n.get_num() as usize;
                let pstr = cell_as_string!(heap[h_offset]);

                pstr_chars = pstr.as_str_from(n).chars().count() - 1;

                if heap[h].get_tag() == HeapCellValueTag::PStrOffset {
                    debug_assert!(heap[h].get_tag() == HeapCellValueTag::PStrOffset);

                    if heap[h_offset].get_tag() == HeapCellValueTag::CStr {
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
                let (name, arity) = cell_as_atom_cell!(heap[s])
                    .get_name_and_arity();

                if name == atom!("[]") && arity == 0 {
                    return CycleSearchResult::EmptyList;
                } else if name == atom!(".") && arity == 2 {
                    s + 2
                } else {
                    return CycleSearchResult::NotList(0, value);
                }
            }
            (HeapCellValueTag::Atom, (name, arity)) => {
                return if name == atom!("[]") && arity == 0 {
                    CycleSearchResult::EmptyList
                } else {
                    CycleSearchResult::NotList(0, value)
                };
            }
            (HeapCellValueTag::AttrVar | HeapCellValueTag::StackVar | HeapCellValueTag::Var) => {
                return CycleSearchResult::PartialList(0, value.as_var().unwrap());
            }
            _ => {
                return CycleSearchResult::NotList(0, value);
            }
        );

        let mut brent_st = BrentAlgState::new(hare);

        brent_st.power += 1; // advance a step.
        brent_st.pstr_chars = pstr_chars;

        loop {
            if let Some(result) = brent_st.cycle_step(heap) {
                return result;
            }
        }
    }

    pub fn detect_cycles_with_max(
        heap: &[HeapCellValue],
        max_steps: usize,
        value: HeapCellValue,
    ) -> CycleSearchResult {
        let mut pstr_chars = 0;

        let hare = read_heap_cell!(value,
            (HeapCellValueTag::Lis, offset) => {
                if max_steps > 0 {
                    offset+1
                } else {
                    return CycleSearchResult::UntouchedList(0, offset);
                }
            }
            (HeapCellValueTag::PStrLoc, h) => {
                let (h_offset, n) = pstr_loc_and_offset(&heap, h);
                let n = n.get_num() as usize;
                let pstr = cell_as_string!(heap[h_offset]);

                pstr_chars = pstr.as_str_from(n).chars().count() - 1;

                if heap[h].get_tag() == HeapCellValueTag::PStrOffset {
                    debug_assert!(heap[h].get_tag() == HeapCellValueTag::PStrOffset);

                    if heap[h_offset].get_tag() == HeapCellValueTag::CStr {
                        return if pstr_chars + 1 <= max_steps {
                            CycleSearchResult::ProperList(pstr_chars + 1)
                        } else {
                            CycleSearchResult::UntouchedCStr(pstr.into(), max_steps)
                        };
                    }
                }

                if pstr_chars + 1 > max_steps {
                    return CycleSearchResult::PStrLocation(max_steps, h_offset);
                }

                h_offset+1
            }
            (HeapCellValueTag::PStrOffset) => {
                unreachable!()
            }
            (HeapCellValueTag::CStr, cstr_atom) => {
                return if max_steps > 0 {
                    let cstr = PartialString::from(cstr_atom);
                    let pstr_chars = cstr.as_str_from(0).chars().count();

                    if pstr_chars <= max_steps {
                        CycleSearchResult::ProperList(pstr_chars)
                    } else {
                        CycleSearchResult::UntouchedCStr(cstr_atom, max_steps)
                    }
                } else {
                    CycleSearchResult::UntouchedCStr(cstr_atom, 0)
                };
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(heap[s]).get_name_and_arity();

                if name == atom!("[]") && arity == 0 {
                    return CycleSearchResult::EmptyList;
                } else if name == atom!(".") && arity == 2 {
                    if max_steps > 0 {
                        s + 2
                    } else {
                        return CycleSearchResult::UntouchedList(0, s + 1);
                    }
                } else {
                    return CycleSearchResult::NotList(0, value);
                }
            }
            (HeapCellValueTag::Atom, (name, arity)) => {
                return if name == atom!("[]") && arity == 0 {
                    CycleSearchResult::EmptyList
                } else {
                    CycleSearchResult::NotList(0, value)
                };
            }
            (HeapCellValueTag::AttrVar | HeapCellValueTag::StackVar | HeapCellValueTag::Var) => {
                return CycleSearchResult::PartialList(0, value.as_var().unwrap());
            }
            _ => {
                return CycleSearchResult::NotList(0, value);
            }
        );

        let mut brent_st = BrentAlgState::new(hare);

        brent_st.power += 1; // advance a step.
        brent_st.pstr_chars = pstr_chars;

        loop {
            if brent_st.num_steps() >= max_steps {
                return brent_st.to_result(&heap);
            }

            if let Some(result) = brent_st.cycle_step(heap) {
                return result;
            }
        }
    }
}

impl MachineState {
    #[inline]
    pub(crate) fn variable_set<S: BuildHasher>(
        &mut self,
        seen_set: &mut IndexSet<HeapCellValue, S>,
        value: HeapCellValue,
    ) {
        let mut iter = stackful_preorder_iter(&mut self.heap, value);

        while let Some(value) = iter.next() {
            let value = unmark_cell_bits!(value);

            if value.is_var() {
                let value = unmark_cell_bits!(heap_bound_store(
                    iter.heap,
                    heap_bound_deref(iter.heap, value)
                ));

                if value.is_var() {
                    seen_set.insert(value);
                }
            }
        }
    }

    fn skip_max_list_cycle(&mut self, lam: usize) {
        fn step(heap: &[HeapCellValue], mut value: HeapCellValue) -> usize {
            loop {
                read_heap_cell!(value,
                    (HeapCellValueTag::PStrLoc, h) => {
                        let (h_offset, _) = pstr_loc_and_offset(&heap, h);
                        return h_offset+1;
                    }
                    (HeapCellValueTag::Lis, h) => {
                        return h+1;
                    }
                    (HeapCellValueTag::Str, s) => {
                        return s+2;
                    }
                    (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
                        value = heap[h];
                    }
                    _ => {
                        unreachable!();
                    }
                );
            }
        }

        let h = self.heap.len();
        self.heap.push(self.registers[3]);

        let mut hare = h;
        let mut tortoise = hare;

        for _ in 0 .. lam {
            hare = step(&self.heap, self.heap[hare]);
        }

        let mut prev_hare = hare;

        while hare != tortoise {
            prev_hare = hare;
            hare = step(&self.heap, self.heap[hare]);
            tortoise = step(&self.heap, self.heap[tortoise]);
        }

        // now compute the num_steps of the list prefix until hare is
        // reached in the fashion of a C do-while loop since hare
        // may point to the beginning of a cycle.

        let mut brent_st = BrentAlgState::new(h);

        brent_st.cycle_step(&self.heap);

        while prev_hare != brent_st.hare {
            brent_st.cycle_step(&self.heap);
        }

        self.heap.pop();

        let target_n = self.store(self.deref(self.registers[1]));
        self.unify_fixnum(Fixnum::build_with(brent_st.num_steps() as i64), target_n);

        if !self.fail {
            unify!(self, self.registers[4], self.heap[prev_hare]);
        }
    }

    fn finalize_skip_max_list(&mut self, n: i64, value: HeapCellValue) {
        let target_n = self.store(self.deref(self.registers[1]));
        self.unify_fixnum(Fixnum::build_with(n), target_n);

        if !self.fail {
            let xs = self.registers[4];
            unify!(self, value, xs);
        }
    }

    fn skip_max_list_result(&mut self, max_steps: i64) {
        let search_result = if max_steps == -1 {
            BrentAlgState::detect_cycles(
                &self.heap,
                self.store(self.deref(self.registers[3])),
            )
        } else {
            BrentAlgState::detect_cycles_with_max(
                &self.heap,
                max_steps as usize,
                self.store(self.deref(self.registers[3])),
            )
        };

        match search_result {
            CycleSearchResult::PStrLocation(steps, pstr_loc) => {
                self.finalize_skip_max_list(steps as i64, pstr_loc_as_cell!(pstr_loc));
            }
            CycleSearchResult::UntouchedList(n, l) => {
                self.finalize_skip_max_list(n as i64, list_loc_as_cell!(l));
            }
            CycleSearchResult::UntouchedCStr(cstr_atom, n) => {
                let cell = if n > 0 {
                    let h = self.heap.len();

                    self.heap.push(string_as_cstr_cell!(cstr_atom));
                    self.heap.push(pstr_offset_as_cell!(h));
                    self.heap.push(fixnum_as_cell!(Fixnum::build_with(n as i64)));

                    pstr_loc_as_cell!(h+1)
                } else {
                    string_as_cstr_cell!(cstr_atom)
                };

                self.finalize_skip_max_list(n as i64, cell);
            }
            CycleSearchResult::EmptyList => {
                self.finalize_skip_max_list(0, empty_list_as_cell!());
            }
            CycleSearchResult::PartialList(n, r) => {
                self.finalize_skip_max_list(n as i64, r.as_heap_cell_value());
            }
            CycleSearchResult::ProperList(steps) => {
                self.finalize_skip_max_list(steps as i64, empty_list_as_cell!())
            }
            CycleSearchResult::NotList(n, value) => {
                self.finalize_skip_max_list(n as i64, value);
            }
            CycleSearchResult::Cyclic(lam) => {
                self.skip_max_list_cycle(lam);
            }
        };
    }

    pub fn skip_max_list(&mut self) -> CallResult {
        let max_steps = self.store(self.deref(self.registers[2]));
        let mut max_old = -1i64;

        if !max_steps.is_var() {
            let max_steps = Number::try_from(max_steps);

            let max_steps_n = match max_steps {
                Ok(Number::Fixnum(n)) => Some(n.get_num()),
                Ok(Number::Integer(n)) => n.to_i64(),
                _ => None,
            };

            if let Some(max_steps) = max_steps_n {
                if max_steps.abs() as usize <= 1 << 63 {
                    if max_steps >= 0 {
                        max_old = max_steps;
                    } else {
                        self.fail = true;
                        return Ok(());
                    }
                } else if max_steps < 0 {
                    self.fail = true;
                    return Ok(());
                }
            } else if !max_steps.map(|n| n.is_integer()).unwrap_or(false) {
                self.fail = true;
                return Ok(());
            }
        }

        self.skip_max_list_result(max_old);
        Ok(())
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

                if value.is_var() {
                    seen_set.insert(value);
                }
            }
        }

        let outcome = heap_loc_as_cell!(
            iter_to_heap_list(
                &mut self.heap,
                seen_set.into_iter(),
            )
        );

        unify_fn!(*self, list_of_vars, outcome);
    }

    #[inline]
    pub(crate) fn install_new_block(&mut self, value: HeapCellValue) -> usize {
        let value = self.store(self.deref(value));

        self.block = self.b;
        self.unify_fixnum(Fixnum::build_with(self.block as i64), value);

        self.block
    }

    pub(crate) fn copy_findall_solution(&mut self, lh_offset: usize, copy_target: HeapCellValue) -> usize {
        let threshold = self.lifted_heap.len() - lh_offset;

        let mut copy_ball_term =
            CopyBallTerm::new(&mut self.stack, &mut self.heap, &mut self.lifted_heap);

        copy_ball_term.push(list_loc_as_cell!(threshold + 1));
        copy_ball_term.push(heap_loc_as_cell!(threshold + 3));
        copy_ball_term.push(heap_loc_as_cell!(threshold + 2));

        copy_term(copy_ball_term, copy_target, AttrVarPolicy::DeepCopy);

        threshold + lh_offset + 2
    }

    #[inline(always)]
    pub(crate) fn truncate_if_no_lifted_heap_diff(
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

    pub(crate) fn get_next_db_ref(&self, indices: &IndexStore, db_ref: &DBRef) -> Option<DBRef> {
        match db_ref {
            DBRef::NamedPred(name, arity) => {
                let key = (*name, *arity);

                if let Some((last_idx, _, _)) = indices.code_dir.get_full(&key) {
                    for idx in last_idx + 1 .. indices.code_dir.len() {
                        let ((name, arity), idx) = indices.code_dir.get_index(idx).unwrap();

                        if idx.is_undefined() {
                            return None;
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

    pub(crate) fn parse_number_from_string(
        &mut self,
        string: &str,
        indices: &IndexStore,
        stub_gen: impl Fn() -> FunctorStub,
    ) -> CallResult {
        let nx = self.store(self.deref(self.registers[2]));

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

        let mut dot_buf: [u8; '.'.len_utf8()] = [0u8];
        '.'.encode_utf8(&mut dot_buf);

        let cursor = std::io::Cursor::new(string);
        let iter = std::io::Read::chain(cursor, std::io::Cursor::new(dot_buf));

        let mut parser = Parser::new(CharReader::new(iter), self);

        match parser.read_term(&CompositeOpDir::new(&indices.op_dir, None)) {
            Err(err) => {
                let err = self.syntax_error(err);
                return Err(self.error_form(err, stub_gen()));
            }
            Ok(Term::Literal(_, Literal::Rational(n))) => {
                self.unify_rational(n, nx);
            }
            Ok(Term::Literal(_, Literal::Float(n))) => {
                self.unify_f64(n.as_ptr(), nx);
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

    pub(crate) fn call_continuation_chunk(&mut self, chunk: HeapCellValue, return_p: usize) -> usize {
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

        self.p = cp + 1;

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
        self.p
    }

    pub fn value_to_str_like(&mut self, value: HeapCellValue) -> Option<AtomOrString> {
        read_heap_cell!(value,
            (HeapCellValueTag::CStr, cstr_atom) => {
                // avoid allocating a String if possible:
                // We must be careful to preserve the string "[]" as is,
                // instead of turning it into the atom [], i.e., "".
                if cstr_atom == atom!("[]") {
                    Some(AtomOrString::String("[]".to_string()))
                } else {
                    Some(AtomOrString::Atom(cstr_atom))
                }
            }
            (HeapCellValueTag::Atom, (atom, arity)) => {
                if arity == 0 {
                    // ... likewise.
                    Some(AtomOrString::Atom(atom))
                } else {
                    None
                }
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.heap[s])
                    .get_name_and_arity();

                if arity == 0 {
                    Some(AtomOrString::Atom(name))
                } else {
                    None
                }
            }
            (HeapCellValueTag::Char, c) => {
                Some(AtomOrString::String(c.to_string()))
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

    pub(crate) fn codes_to_string(
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

    pub(crate) fn strip_module(
        &self,
        mut qualified_goal: HeapCellValue,
        mut module_loc: HeapCellValue,
    ) -> (HeapCellValue, HeapCellValue) {
        loop {
            read_heap_cell!(qualified_goal,
                (HeapCellValueTag::Str, s) => {
                    let (name, arity) = cell_as_atom_cell!(self.heap[s])
                        .get_name_and_arity();

                    if name == atom!(":") && arity == 2 {
                        module_loc = self.heap[s+1];
                        qualified_goal = self.heap[s+2];
                    } else {
                        break;
                    }
                }
                (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
                    if qualified_goal != self.heap[h] {
                        qualified_goal = self.heap[h];
                    } else {
                        break;
                    }
                }
                _ => {
                    break;
                }
            );
        }

        (module_loc, qualified_goal)
    }
}

impl Machine {
    #[inline(always)]
    pub(crate) fn call_inline(
        &mut self,
        arity: usize,
        call_at_index: impl Fn(&mut Machine, Atom, usize, IndexPtr) -> CallResult,
    ) -> CallResult {
        let arity = arity - 1;
        let goal = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));

        let load_registers = |machine_st: &mut MachineState, goal: HeapCellValue| -> Option<PredicateKey> {
            read_heap_cell!(goal,
                (HeapCellValueTag::Str, s) => {
                    let (name, goal_arity) = cell_as_atom_cell!(machine_st.heap[s])
                        .get_name_and_arity();

                    if goal_arity > 0 {
                        for idx in (1 .. arity + 1).rev() {
                            machine_st.registers[idx + goal_arity] = machine_st.registers[idx + 1];
                        }
                    } else {
                        for idx in 1 .. arity + 1 {
                            machine_st.registers[idx] = machine_st.registers[idx + 1];
                        }
                    }

                    for idx in 1 .. goal_arity + 1 {
                        machine_st.registers[idx] = machine_st.heap[s+idx];
                    }

                    Some((name, goal_arity))
                }
                _ => {
                    unreachable!()
                }
            )
        };

        read_heap_cell!(goal,
            (HeapCellValueTag::Str, s) => {
                let goal_arity = cell_as_atom_cell!(self.machine_st.heap[s]).get_arity();

                if self.machine_st.heap.len() > s + goal_arity + 1 {
                    let index_cell = self.machine_st.heap[s+goal_arity+1];

                    if let Some(code_index) = get_structure_index(index_cell) {
                        if code_index.is_undefined() {
                            self.machine_st.fail = true;
                            return Ok(());
                        }

                        match load_registers(&mut self.machine_st, goal) {
                            Some((name, goal_arity)) => {
                                let arity = goal_arity + arity;
                                self.machine_st.neck_cut();
                                return call_at_index(self, name, arity, code_index.get());
                            }
                            None => {
                            }
                        }
                    }
                }
            }
            _ => {
            }
        );

        self.machine_st.fail = true;
        Ok(())
    }

    #[inline(always)]
    pub(crate) fn compile_inline_or_expanded_goal(&mut self) -> CallResult {
        let goal = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
        let module_name = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[4]));

        // supp_vars are the supplementary variables generated by
        // complete_partial_goal prior to goal_expansion.
        let mut supp_vars = IndexSet::with_hasher(FxBuildHasher::default());

        self.machine_st.variable_set(&mut supp_vars, self.machine_st.registers[2]);

        struct GoalAnalysisResult {
            is_simple_goal: bool,
            goal: HeapCellValue,
            key: PredicateKey,
            expanded_vars: IndexSet<HeapCellValue, BuildHasherDefault<FxHasher>>,
            supp_vars: IndexSet<HeapCellValue, BuildHasherDefault<FxHasher>>,
        }

        let result = read_heap_cell!(goal,
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.machine_st.heap[s])
                    .get_name_and_arity();

                let mut expanded_vars = IndexSet::with_hasher(FxBuildHasher::default());

                // fill expanded_vars with variables of the partial
                // goal pre-completion by complete_partial_goal.
                for idx in s + 1 .. s + arity - supp_vars.len() + 1 {
                    self.machine_st.variable_set(&mut expanded_vars, self.machine_st.heap[idx]);
                }

                let is_simple_goal = if arity >= supp_vars.len() {
                    // post_supp_args are the arguments to the
                    // post-expansion complete goal gathered from the
                    // final supp_vars.len() arguments. they must
                    // agree in supp_vars in order of entry of
                    // insertion as well as the previous
                    // supp_vars.len() argument's variables being
                    // disjoint from them. if they are not, the
                    // expanded goal are not simple.

                    let post_supp_args = self.machine_st.heap[s+arity-supp_vars.len()+1 .. s+arity+1]
                        .iter()
                        .cloned();

                    post_supp_args
                        .zip(supp_vars.iter())
                        .all(|(arg_term, supp_var)| {
                            let arg_term = self.machine_st.store(self.machine_st.deref(arg_term));

                            if arg_term.is_var() && supp_var.is_var() {
                                return arg_term == *supp_var;
                            }

                            false
                        }) && expanded_vars.intersection(&supp_vars).next().is_none()
                } else {
                    false
                };

                let goal = if is_simple_goal {
                    let h = self.machine_st.heap.len();
                    let arity = arity - supp_vars.len();

                    for idx in 0 .. arity + 1 {
                        let value = self.machine_st.heap[s + idx];
                        self.machine_st.heap.push(value);
                    }

                    self.machine_st.heap[h] = atom_as_cell!(name, arity);

                    str_loc_as_cell!(h)
                } else {
                    goal
                };

                GoalAnalysisResult {
                    is_simple_goal,
                    goal,
                    key: (name, arity),
                    expanded_vars,
                    supp_vars
                }
            }
            (HeapCellValueTag::Atom, (name, arity)) => {
                debug_assert_eq!(arity, 0);

                let h = self.machine_st.heap.len();
                self.machine_st.heap.push(goal);

                GoalAnalysisResult {
                    is_simple_goal: true,
                    goal: str_loc_as_cell!(h),
                    key: (name, 0),
                    expanded_vars: IndexSet::with_hasher(FxBuildHasher::default()),
                    supp_vars,
                }
            }
            (HeapCellValueTag::Char, c) => {
                let name = self.machine_st.atom_tbl.build_with(&c.to_string());

                let h = self.machine_st.heap.len();
                self.machine_st.heap.push(atom_as_cell!(name));

                GoalAnalysisResult {
                    is_simple_goal: true,
                    goal: str_loc_as_cell!(h),
                    key: (name, 0),
                    expanded_vars: IndexSet::with_hasher(FxBuildHasher::default()),
                    supp_vars,
                }
            }
            _ => {
                self.machine_st.fail = true;
                return Ok(());
            }
        );

        if result.key.0 == atom!(":") {
            self.machine_st.fail = true;
            return Ok(());
        }

        let expanded_term = if result.is_simple_goal {
            let idx = self.get_or_insert_qualified_code_index(module_name, result.key);
            self.machine_st.heap.push(untyped_arena_ptr_as_cell!(UntypedArenaPtr::from(idx)));
            result.goal
        } else {
            // all supp_vars must appear later!
            let vars = IndexSet::<HeapCellValue, BuildHasherDefault<FxHasher>>::from_iter(
                result.expanded_vars.difference(&result.supp_vars).cloned()
            );

            let vars: Vec<_> = vars
                .union(&result.supp_vars) // difference + union does not cancel.
                .map(|v| Term::Var(Cell::default(), Rc::new(format!("_{}", v.get_value()))))
                .collect();

            let helper_clause_loc = self.code.len();

            match self.compile_standalone_clause(temp_v!(1), &vars) {
                Err(e) => {
                    let err = self.machine_st.session_error(e);
                    let stub = functor_stub(atom!("call"), result.key.1);

                    return Err(self.machine_st.error_form(err, stub));
                }
                Ok(()) => {
                    let h = self.machine_st.heap.len();

                    self.machine_st.heap.push(atom_as_cell!(atom!("$aux"), 0));

                    for value in result.expanded_vars.difference(&result.supp_vars).cloned() {
                        self.machine_st.heap.push(value);
                    }

                    let anon_str_arity = self.machine_st.heap.len() - h - 1;

                    self.machine_st.heap[h] = atom_as_cell!(atom!("$aux"), anon_str_arity);

                    let idx = CodeIndex::new(
                        IndexPtr::index(helper_clause_loc),
                        &mut self.machine_st.arena,
                    );

                    self.machine_st.heap.push(untyped_arena_ptr_as_cell!(UntypedArenaPtr::from(idx)));

                    str_loc_as_cell!(h)
                }
            }
        };

        let truncated_goal = self.machine_st.registers[3];
        unify!(&mut self.machine_st, expanded_term, truncated_goal);

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn is_expanded_or_inlined(&self) -> bool {
        let (_module_loc, qualified_goal) = self.machine_st.strip_module(
            self.machine_st.registers[1],
            empty_list_as_cell!(),
        );

        if HeapCellValueTag::Str == qualified_goal.get_tag() {
            let s = qualified_goal.get_value();
            let (name, arity) = cell_as_atom_cell!(self.machine_st.heap[s])
                .get_name_and_arity();

            if name == atom!("$call") {
                return false;
            }

            if self.machine_st.heap.len() > s + 1 + arity {
                let idx_cell = self.machine_st.heap[s + 1 + arity];

                if HeapCellValueTag::Cons == idx_cell.get_tag() {
                    match_untyped_arena_ptr!(cell_as_untyped_arena_ptr!(idx_cell),
                        (ArenaHeaderTag::IndexPtr, _ip) => {
                            return true;
                        }
                        _ => {
                        }
                    );
                }
            }
        }

        false
    }

    #[inline(always)]
    pub(crate) fn prepare_call_clause(&mut self, arity: usize) -> CallResult {
        let (module_loc, qualified_goal) = self.machine_st.strip_module(
            self.machine_st.registers[3],
            self.machine_st.registers[2],
        );

        // the first three arguments don't belong to the containing call/N.
        let arity = arity - 3;

        let (name, narity, s) = self.machine_st.setup_call_n_init_goal_info(
            qualified_goal,
            arity,
        )?;

        let module_loc = self.machine_st.store(self.machine_st.deref(module_loc));

        if module_loc.is_var() {
            self.load_context_module(module_loc);

            if self.machine_st.fail {
                self.machine_st.fail = false;
                self.machine_st.unify_atom(atom!("user"), module_loc);

                if self.machine_st.fail {
                    return Ok(());
                }
            }
        }

        let target_module_loc = self.machine_st.registers[2];

        unify_fn!(
            &mut self.machine_st,
            module_loc,
            target_module_loc
        );

        if self.machine_st.fail {
            return Ok(());
        }

        // assemble goal from pre-loaded (narity) and supplementary
        // (arity) arguments.

        let target_goal = if arity == 0 {
            qualified_goal
        } else { // if narity + arity > 0 {
            let h = self.machine_st.heap.len();
            self.machine_st.heap.push(atom_as_cell!(name, narity + arity));

            for idx in 1 .. narity + 1 {
                self.machine_st.heap.push(self.machine_st.heap[s + idx]);
            }

            for idx in 1 .. arity + 1 {
                self.machine_st.heap.push(self.machine_st.registers[3 + idx]);
            }

            let index_cell = self.machine_st.heap[s + narity + 1];

            if get_structure_index(index_cell).is_some() {
                self.machine_st.heap.push(index_cell);
                str_loc_as_cell!(h)
            } else if narity + arity > 0 {
                str_loc_as_cell!(h)
            } else {
                heap_loc_as_cell!(h)
            }
        };

        let target_qualified_goal = self.machine_st.registers[1];

        unify_fn!(
            &mut self.machine_st,
            target_goal,
            target_qualified_goal
        );

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn is_reset_cont_marker(&self, p: usize) -> bool {
        match &self.code[p] {
            &Instruction::CallResetContinuationMarker(_) |
            &Instruction::ExecuteResetContinuationMarker(_) => true,
            _ => false
        }
    }

    #[inline(always)]
    pub(crate) fn bind_from_register(&mut self) {
        let reg = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));
        let n = match Number::try_from(reg) {
            Ok(Number::Fixnum(n)) => usize::try_from(n.get_num()).ok(),
            Ok(Number::Integer(n)) => n.to_usize(),
            _ => {
                unreachable!()
            }
        };

        if let Some(n) = n {
            if n <= MAX_ARITY {
                let target = self.machine_st.registers[n];
                let addr = self.machine_st.registers[1];

                unify_fn!(self.machine_st, addr, target);
                return;
            }
        }

        self.machine_st.fail = true;
    }

    #[inline(always)]
    pub(crate) fn current_hostname(&mut self) {
        match hostname::get().ok() {
            Some(host) => match host.to_str() {
                Some(host) => {
                    let hostname = self.machine_st.atom_tbl.build_with(host);

                    self.machine_st.unify_atom(
                        hostname,
                        self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]))
                    );

                    return;
                }
                None => {}
            },
            None => {}
        }

        self.machine_st.fail = true;
    }

    #[inline(always)]
    pub(crate) fn current_input(&mut self) -> CallResult {
        let addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
        let stream = self.user_input;

        if let Some(var) = addr.as_var() {
            self.machine_st.bind(var, stream_as_cell!(stream));
            return Ok(());
        }

        read_heap_cell!(addr,
            (HeapCellValueTag::Cons, cons_ptr) => {
                match_untyped_arena_ptr!(cons_ptr,
                    (ArenaHeaderTag::Stream, other_stream) => {
                        self.machine_st.fail = stream != other_stream;
                    }
                    _ => {
                        let stub = functor_stub(atom!("current_input"), 1);
                        let err = self.machine_st.domain_error(DomainErrorType::Stream, addr);

                        return Err(self.machine_st.error_form(err, stub));
                    }
                );
            }
            _ => {
                let stub = functor_stub(atom!("current_input"), 1);
                let err = self.machine_st.domain_error(DomainErrorType::Stream, addr);

                return Err(self.machine_st.error_form(err, stub));
            }
        );

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn current_output(&mut self) -> CallResult {
        let addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
        let stream = self.user_output;

        if let Some(var) = addr.as_var() {
            self.machine_st.bind(var, stream_as_cell!(stream));
            return Ok(());
        }

        read_heap_cell!(addr,
            (HeapCellValueTag::Cons, cons_ptr) => {
                match_untyped_arena_ptr!(cons_ptr,
                    (ArenaHeaderTag::Stream, other_stream) => {
                        self.machine_st.fail = stream != other_stream;
                    }
                    _ => {
                        let stub = functor_stub(atom!("current_output"), 1);
                        let err = self.machine_st.domain_error(DomainErrorType::Stream, addr);

                        return Err(self.machine_st.error_form(err, stub));
                    }
                );
            }
            _ => {
                let stub = functor_stub(atom!("current_output"), 1);
                let err = self.machine_st.domain_error(DomainErrorType::Stream, addr);

                return Err(self.machine_st.error_form(err, stub));
            }
        );

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn directory_files(&mut self) -> CallResult {
        if let Some(dir) = self.machine_st.value_to_str_like(self.machine_st.registers[1]) {
            let path = std::path::Path::new(dir.as_str());
            let mut files = Vec::new();

            if let Ok(entries) = fs::read_dir(path) {
                for entry in entries {
                    if let Ok(entry) = entry {
                        if let Some(name) = entry.file_name().to_str() {
                            let name = self.machine_st.atom_tbl.build_with(name);
                            files.push(atom_as_cstr_cell!(name));

                            continue;
                        }
                    }

                    let stub = functor_stub(atom!("directory_files"), 2);
                    let err = self.machine_st.representation_error(RepFlag::Character);
                    let err = self.machine_st.error_form(err, stub);

                    return Err(err);
                }

                let files_list = heap_loc_as_cell!(
                    iter_to_heap_list(&mut self.machine_st.heap, files.into_iter())
                );

                unify!(self.machine_st, self.machine_st.registers[2], files_list);
                return Ok(());
            }
        }

        self.machine_st.fail = true;
        Ok(())
    }

    #[inline(always)]
    pub(crate) fn file_size(&mut self) {
        if let Some(file) = self.machine_st.value_to_str_like(self.machine_st.registers[1]) {
            let len = Number::arena_from(
                fs::metadata(file.as_str()).unwrap().len(),
                &mut self.machine_st.arena,
            );

            match len {
                Number::Fixnum(n) => self.machine_st.unify_fixnum(n, self.machine_st.registers[2]),
                Number::Integer(n) => self.machine_st.unify_big_int(n, self.machine_st.registers[2]),
                _ => unreachable!(),
            }
        } else {
            self.machine_st.fail = true;
        }
    }

    #[inline(always)]
    pub(crate) fn file_exists(&mut self) {
        if let Some(file) = self.machine_st.value_to_str_like(self.machine_st.registers[1]) {
            let file_str = file.as_str();

            if !std::path::Path::new(file_str).exists() || !fs::metadata(file_str).unwrap().is_file() {
                self.machine_st.fail = true;
            }
        } else {
            self.machine_st.fail = true;
        }
    }

    #[inline(always)]
    pub(crate) fn directory_exists(&mut self) {
        if let Some(dir) = self.machine_st.value_to_str_like(self.machine_st.registers[1]) {
            let dir_str = dir.as_str();

            if !std::path::Path::new(dir_str).exists() || !fs::metadata(dir_str).unwrap().is_dir() {
                self.machine_st.fail = true;
            }
        } else {
            self.machine_st.fail = true;
        }
    }

    #[inline(always)]
    pub(crate) fn file_time(&mut self) {
        if let Some(file) = self.machine_st.value_to_str_like(self.machine_st.registers[1]) {
            let which = cell_as_atom!(self.machine_st.store(self.machine_st.deref(
                self.machine_st.registers[2]
            )));

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

                    self.machine_st.unify_complete_string(
                        chars_atom,
                        self.machine_st.registers[3],
                    );

                    return;
                }
            }
        }

        self.machine_st.fail = true;
    }

    #[inline(always)]
    pub(crate) fn directory_separator(&mut self) {
        self.machine_st.unify_char(std::path::MAIN_SEPARATOR, self.machine_st.registers[1]);
    }

    #[inline(always)]
    pub(crate) fn make_directory(&mut self) {
        if let Some(dir) = self.machine_st.value_to_str_like(self.machine_st.registers[1]) {
            match fs::create_dir(dir.as_str()) {
                Ok(_) => {}
                _ => {
                    self.machine_st.fail = true;
                }
            }
        } else {
            self.machine_st.fail = true;
        }
    }

    #[inline(always)]
    pub(crate) fn make_directory_path(&mut self) {
        if let Some(dir) = self.machine_st.value_to_str_like(self.machine_st.registers[1]) {

            match fs::create_dir_all(dir.as_str()) {
                Ok(_) => {}
                _ => {
                    self.machine_st.fail = true;
                }
            }
        } else {
            self.machine_st.fail = true;
        }
    }

    #[inline(always)]
    pub(crate) fn delete_file(&mut self) {
        if let Some(file) = self.machine_st.value_to_str_like(self.machine_st.registers[1]) {
            match fs::remove_file(file.as_str()) {
                Ok(_) => {}
                _ => {
                    self.machine_st.fail = true;
                }
            }
        }
    }

    #[inline(always)]
    pub(crate) fn rename_file(&mut self) {
        if let Some(file) = self.machine_st.value_to_str_like(self.machine_st.registers[1]) {
            if let Some(renamed) = self.machine_st.value_to_str_like(self.machine_st.registers[2]) {
                if fs::rename(file.as_str(), renamed.as_str()).is_ok() {
                    return;
                }
            }
        }

        self.machine_st.fail = true;
    }

    #[inline(always)]
    pub(crate) fn delete_directory(&mut self) {
        if let Some(dir) = self.machine_st.value_to_str_like(self.machine_st.registers[1]) {
            match fs::remove_dir(dir.as_str()) {
                Ok(_) => {}
                _ => {
                    self.machine_st.fail = true;
                }
            }
        }
    }

    #[inline(always)]
    pub(crate) fn working_directory(&mut self) -> CallResult {
        if let Ok(dir) = env::current_dir() {
            let current = match dir.to_str() {
                Some(d) => d,
                _ => {
                    let stub = functor_stub(atom!("working_directory"), 2);
                    let err = self.machine_st.representation_error(RepFlag::Character);
                    let err = self.machine_st.error_form(err, stub);

                    return Err(err);
                }
            };

            let current_atom = self.machine_st.atom_tbl.build_with(&current);

            self.machine_st.unify_complete_string(
                current_atom,
                self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1])),
            );

            if self.machine_st.fail {
                return Ok(());
            }

            let target = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));

            if let Some(next) = self.machine_st.value_to_str_like(target) {
                if env::set_current_dir(std::path::Path::new(next.as_str())).is_ok() {
                    return Ok(());
                }
            }
        }

        self.machine_st.fail = true;
        Ok(())
    }

    #[inline(always)]
    pub(crate) fn path_canonical(&mut self) -> CallResult {
        if let Some(path) = self.machine_st.value_to_str_like(self.machine_st.registers[1]) {
            match fs::canonicalize(path.as_str()) {
                Ok(canonical) => {
                    let cs = match canonical.to_str() {
                        Some(s) => s,
                        _ => {
                            let stub = functor_stub(atom!("path_canonical"), 2);
                            let err = self.machine_st.representation_error(RepFlag::Character);
                            let err = self.machine_st.error_form(err, stub);

                            return Err(err);
                        }
                    };

                    let canonical_atom = self.machine_st.atom_tbl.build_with(cs);

                    self.machine_st.unify_complete_string(
                        canonical_atom,
                        self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2])),
                    );

                    return Ok(());
                }
                _ => {
                }
            }
        }

        self.machine_st.fail = true;
        Ok(())
    }

    #[inline(always)]
    pub(crate) fn atom_chars(&mut self) {
        let a1 = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));

        read_heap_cell!(a1,
            (HeapCellValueTag::Char) => {
                let h = self.machine_st.heap.len();

                self.machine_st.heap.push(a1);
                self.machine_st.heap.push(empty_list_as_cell!());

                unify!(self.machine_st, self.machine_st.registers[2], list_loc_as_cell!(h));
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.machine_st.heap[s])
                    .get_name_and_arity();

                if arity == 0 {
                    self.machine_st.unify_complete_string(
                        name,
                        self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2])),
                    );
                } else {
                    self.machine_st.fail = true;
                }
            }
            (HeapCellValueTag::Atom, (name, arity)) => {
                if arity == 0 {
                    self.machine_st.unify_complete_string(
                        name,
                        self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2])),
                    );
                } else {
                    self.machine_st.fail = true;
                }
            }
            (HeapCellValueTag::Var | HeapCellValueTag::AttrVar | HeapCellValueTag::StackVar) => {
                let a2 = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));

                if let Some(str_like) = self.machine_st.value_to_str_like(a2) {
                    let atom_cell = match str_like {
                        AtomOrString::Atom(atom) => {
                            atom_as_cell!(if atom == atom!("[]") {
                                self.machine_st.atom_tbl.build_with("")
                            } else {
                                atom
                            })
                        }
                        AtomOrString::String(string) => {
                            atom_as_cell!(self.machine_st.atom_tbl.build_with(&string))
                        }
                    };

                    self.machine_st.bind(a1.as_var().unwrap(), atom_cell);
                    return;
                }

                self.machine_st.fail = true;
            }
            _ => {
                unreachable!();
            }
        );
    }

    #[inline(always)]
    pub(crate) fn atom_codes(&mut self) -> CallResult {
        let a1 = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));

        read_heap_cell!(a1,
            (HeapCellValueTag::Char, c) => {
                let h = self.machine_st.heap.len();

                self.machine_st.heap.push(fixnum_as_cell!(Fixnum::build_with(c as i64)));
                self.machine_st.heap.push(empty_list_as_cell!());

                unify!(self.machine_st, list_loc_as_cell!(h), self.machine_st.registers[2]);
            }
            (HeapCellValueTag::Atom, (name, arity)) => {
                if arity == 0 {
                    let iter = name.chars()
                        .map(|c| fixnum_as_cell!(Fixnum::build_with(c as i64)));

                    let h = iter_to_heap_list(&mut self.machine_st.heap, iter);
                    unify!(self.machine_st, heap_loc_as_cell!(h), self.machine_st.registers[2]);
                } else {
                    self.machine_st.fail = true;
                }
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.machine_st.heap[s])
                    .get_name_and_arity();

                if arity == 0 {
                    let iter = name.chars()
                        .map(|c| fixnum_as_cell!(Fixnum::build_with(c as i64)));

                    let h = iter_to_heap_list(&mut self.machine_st.heap, iter);
                    unify!(self.machine_st, heap_loc_as_cell!(h), self.machine_st.registers[2]);
                } else {
                    self.machine_st.fail = true;
                }
            }
            (HeapCellValueTag::Var | HeapCellValueTag::AttrVar | HeapCellValueTag::StackVar) => {
                let stub_gen = || functor_stub(atom!("atom_codes"), 2);

                match self.machine_st.try_from_list(self.machine_st.registers[2], stub_gen) {
                    Ok(addrs) => {
                        let string = self.machine_st.codes_to_string(addrs.into_iter(), stub_gen)?;
                        let atom = self.machine_st.atom_tbl.build_with(&string);

                        self.machine_st.bind(a1.as_var().unwrap(), atom_as_cell!(atom));
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

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn atom_length(&mut self) {
        let a1 = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));

        let len: i64 = read_heap_cell!(a1,
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.machine_st.heap[s])
                    .get_name_and_arity();

                if arity == 0 {
                    name.chars().count() as i64
                } else {
                    self.machine_st.fail = true;
                    return;
                }
            }
            (HeapCellValueTag::Atom, (name, arity)) => {
                if arity == 0 {
                    name.chars().count() as i64
                } else {
                    self.machine_st.fail = true;
                    return;
                }
            }
            (HeapCellValueTag::Char) => {
                1
            }
            _ => {
                unreachable!()
            }
        );

        self.machine_st.unify_fixnum(
            Fixnum::build_with(len),
            self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2])),
        );
    }

    #[inline(always)]
    pub(crate) fn call_continuation(&mut self, last_call: bool) -> CallResult {
        let stub_gen = || functor_stub(atom!("call_continuation"), 1);
        let a1 = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));

        match self.machine_st.try_from_list(a1, stub_gen) {
            Err(e) => Err(e),
            Ok(cont_chunks) => {
                let mut return_p = if last_call {
                    self.machine_st.cp
                } else {
                    self.machine_st.p + 1
                };

                self.machine_st.p = return_p;

                for chunk in cont_chunks.into_iter().rev() {
                    return_p = self.machine_st.call_continuation_chunk(chunk, return_p);
                }

                Ok(())
            }
        }
    }

    #[inline(always)]
    pub(crate) fn chars_to_number(&mut self) -> CallResult {
        let stub_gen = || functor_stub(atom!("number_chars"), 2);
        let a1 = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
        let atom_or_string = self.machine_st.value_to_str_like(a1).unwrap();

        self.machine_st.parse_number_from_string(
            atom_or_string.as_str(),
            &self.indices,
            stub_gen,
        )
    }

    #[inline(always)]
    pub(crate) fn create_partial_string(&mut self) {
        let atom = cell_as_atom!(
            self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]))
        );

        if atom == atom!("") {
            self.machine_st.fail = true;
            return;
        }

        let pstr_h = self.machine_st.heap.len();

        self.machine_st.heap.push(pstr_as_cell!(atom));
        self.machine_st.heap.push(heap_loc_as_cell!(pstr_h+1));

        unify!(self.machine_st, self.machine_st.registers[2], pstr_loc_as_cell!(pstr_h));

        if !self.machine_st.fail {
            let tail = self.machine_st.registers[3];
            unify!(self.machine_st, tail, heap_loc_as_cell!(pstr_h+1));
        }
    }

    #[inline(always)]
    pub(crate) fn is_partial_string(&mut self) {
        let value = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));

        let h = self.machine_st.heap.len();
        self.machine_st.heap.push(value);

        let mut iter = HeapPStrIter::new(&self.machine_st.heap, h);

        while let Some(_) = iter.next() {}

        let at_end_of_pstr = iter.focus.is_var() || iter.at_string_terminator();
        self.machine_st.fail = !at_end_of_pstr;

        self.machine_st.heap.pop();
    }

    #[inline(always)]
    pub(crate) fn partial_string_tail(&mut self) {
        let pstr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));

        read_heap_cell!(pstr,
            (HeapCellValueTag::PStrLoc, h) => {
                let (h, _) = pstr_loc_and_offset(&self.machine_st.heap, h);

                if HeapCellValueTag::CStr == self.machine_st.heap[h].get_tag() {
                    self.machine_st.unify_atom(
                        atom!("[]"),
                        self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]))
                    );
                } else {
                    unify_fn!(
                        self.machine_st,
                        heap_loc_as_cell!(h+1),
                        self.machine_st.registers[2]
                    );
                }
            }
            (HeapCellValueTag::CStr) => {
                self.machine_st.unify_atom(
                    atom!("[]"),
                    self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]))
                );
            }
            (HeapCellValueTag::Lis, h) => {
                unify_fn!(
                    self.machine_st,
                    heap_loc_as_cell!(h+1),
                    self.machine_st.registers[2]
                );
            }
            _ => {
                self.machine_st.fail = true;
            }
        );
    }

    #[inline(always)]
    pub(crate) fn peek_byte(&mut self) -> CallResult {
        let stub_gen = || functor_stub(atom!("peek_byte"), 2);

        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices.stream_aliases,
            atom!("peek_byte"),
            2,
        )?;

        self.machine_st.check_stream_properties(
            stream,
            StreamType::Binary,
            Some(self.machine_st.registers[2]),
            atom!("peek_byte"),
            2,
        )?;

        if stream.past_end_of_stream() {
            if EOFAction::Reset != stream.options().eof_action() {
                return Ok(());
            } else if self.machine_st.fail {
                return Ok(());
            }
        }

        if stream.at_end_of_stream() {
            stream.set_past_end_of_stream(true);

            self.machine_st.unify_fixnum(
                Fixnum::build_with(-1),
                self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2])),
            );

            return Ok(());
        }

        let addr = match self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2])) {
            addr if addr.is_var() => addr,
            addr => match Number::try_from(addr) {
                Ok(Number::Integer(n)) => {
                    if let Some(nb) = n.to_u8() {
                        fixnum_as_cell!(Fixnum::build_with(nb as i64))
                    } else {
                        let err = self.machine_st.type_error(ValidType::InByte, addr);
                        return Err(self.machine_st.error_form(err, stub_gen()));
                    }
                }
                Ok(Number::Fixnum(n)) => {
                    if let Ok(nb) = u8::try_from(n.get_num()) {
                        fixnum_as_cell!(Fixnum::build_with(nb as i64))
                    } else {
                        let err = self.machine_st.type_error(ValidType::InByte, addr);
                        return Err(self.machine_st.error_form(err, stub_gen()));
                    }
                }
                _ => {
                    let err = self.machine_st.type_error(ValidType::InByte, addr);
                    return Err(self.machine_st.error_form(err, stub_gen()));
                }
            },
        };

        loop {
            match stream.peek_byte().map_err(|e| e.kind()) {
                Ok(b) => {
                    self.machine_st.unify_fixnum(Fixnum::build_with(b as i64), addr);
                }
                Err(ErrorKind::PermissionDenied) => {
                    self.machine_st.fail = true;
                    break;
                }
                _ => {
                    self.machine_st.eof_action(
                        self.machine_st.registers[2],
                        stream,
                        atom!("peek_byte"),
                        2,
                    )?;

                    if EOFAction::Reset != stream.options().eof_action() {
                        break;
                    } else if self.machine_st.fail {
                        break;
                    }
                }
            }
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn peek_char(&mut self) -> CallResult {
        let stub_gen = || functor_stub(atom!("peek_char"), 2);

        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices.stream_aliases,
            atom!("peek_char"),
            2,
        )?;

        self.machine_st.check_stream_properties(
            stream,
            StreamType::Text,
            Some(self.machine_st.registers[2]),
            atom!("peek_char"),
            2,
        )?;

        if stream.past_end_of_stream() {
            if EOFAction::Reset != stream.options().eof_action() {
                return Ok(());
            } else if self.machine_st.fail {
                return Ok(());
            }
        }

        if stream.at_end_of_stream() {
            let end_of_file = atom!("end_of_file");
            stream.set_past_end_of_stream(true);

            self.machine_st.unify_atom(
                end_of_file,
                self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2])),
            );

            return Ok(());
        }

        let a2 = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));

        let a2 = read_heap_cell!(a2,
            (HeapCellValueTag::Char) => {
                a2
            }
            (HeapCellValueTag::Atom, (name, arity)) => {
                if arity == 0 {
                    if let Some(c) = name.as_char() {
                        char_as_cell!(c)
                    } else {
                        let err = self.machine_st.type_error(ValidType::InCharacter, a2);
                        return Err(self.machine_st.error_form(err, stub_gen()));
                    }
                } else {
                    let err = self.machine_st.type_error(ValidType::InCharacter, a2);
                    return Err(self.machine_st.error_form(err, stub_gen()));
                }
            }
            (HeapCellValueTag::Var | HeapCellValueTag::StackVar | HeapCellValueTag::AttrVar) => {
                a2
            }
            _ => {
                let err = self.machine_st.type_error(ValidType::InCharacter, a2);
                return Err(self.machine_st.error_form(err, stub_gen()));
            }
        );

        loop {
            match stream.peek_char().map(|result| result.map_err(|e| e.kind())) {
                Some(Ok(d)) => {
                    self.machine_st.unify_char(d, a2);
                    break;
                }
                Some(Err(ErrorKind::PermissionDenied)) => {
                    self.machine_st.fail = true;
                    break;
                }
                _ => {
                    self.machine_st.eof_action(
                        self.machine_st.registers[2],
                        stream,
                        atom!("peek_char"),
                        2,
                    )?;

                    if EOFAction::Reset != stream.options().eof_action() {
                        break;
                    } else if self.machine_st.fail {
                        break;
                    }
                }
            }
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn peek_code(&mut self) -> CallResult {
        let stub_gen = || functor_stub(atom!("peek_code"), 2);

        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices.stream_aliases,
            atom!("peek_code"),
            2,
        )?;

        self.machine_st.check_stream_properties(
            stream,
            StreamType::Text,
            Some(self.machine_st.registers[2]),
            atom!("peek_code"),
            2,
        )?;

        if stream.past_end_of_stream() {
            if EOFAction::Reset != stream.options().eof_action() {
                return Ok(());
            } else if self.machine_st.fail {
                return Ok(());
            }
        }

        if stream.at_end_of_stream() {
            let end_of_file = atom!("end_of_file");
            stream.set_past_end_of_stream(true);

            self.machine_st.unify_atom(
                end_of_file,
                self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2])),
            );

            return Ok(());
        }

        let a2 = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));

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
                            let err = self.machine_st.representation_error(RepFlag::InCharacterCode);
                            return Err(self.machine_st.error_form(err, stub_gen()));
                        }
                    }
                    Ok(Number::Fixnum(n)) => {
                        let n = u32::try_from(n.get_num())
                            .ok()
                            .and_then(|n| std::char::from_u32(n).and_then(|_| Some(n)));

                        if let Some(n) = n {
                            fixnum_as_cell!(Fixnum::build_with(n as i64))
                        } else {
                            let err = self.machine_st.representation_error(RepFlag::InCharacterCode);
                            return Err(self.machine_st.error_form(err, stub_gen()));
                        }
                    }
                    _ => {
                        let err = self.machine_st.type_error(ValidType::Integer, self.machine_st.registers[2]);
                        return Err(self.machine_st.error_form(err, stub_gen()));
                    }
                }
            }
        );

        loop {
            let result = stream.peek_char();

            match result.map(|result| result.map_err(|e| e.kind())) {
                Some(Ok(c)) => {
                    self.machine_st.unify_fixnum(Fixnum::build_with(c as i64), addr);
                    break;
                }
                Some(Err(ErrorKind::PermissionDenied)) => {
                    self.machine_st.fail = true;
                    break;
                }
                _ => {
                    self.machine_st.eof_action(
                        self.machine_st.registers[2],
                        stream,
                        atom!("peek_code"),
                        2,
                    )?;

                    if EOFAction::Reset != stream.options().eof_action() {
                        break;
                    } else if self.machine_st.fail {
                        break;
                    }
                }
            }
        }

        return Ok(());
    }

    #[inline(always)]
    pub(crate) fn number_to_chars(&mut self) {
        let n = self.machine_st.registers[1];
        let chs = self.machine_st.registers[2];

        let n = self.machine_st.store(self.machine_st.deref(n));

        let string = match Number::try_from(n) {
            Ok(Number::Float(OrderedFloat(n))) => {
                fmt_float(n)
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

        let chars_atom = self.machine_st.atom_tbl.build_with(&string.trim());
        self.machine_st.unify_complete_string(
            chars_atom,
            self.machine_st.store(self.machine_st.deref(chs)),
        );
    }

    #[inline(always)]
    pub(crate) fn number_to_codes(&mut self) {
        let n = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
        let chs = self.machine_st.registers[2];

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

        let h = iter_to_heap_list(&mut self.machine_st.heap, codes);
        unify!(self.machine_st, heap_loc_as_cell!(h), chs);
    }

    #[inline(always)]
    pub(crate) fn codes_to_number(&mut self) -> CallResult {
        let stub_gen = || functor_stub(atom!("number_codes"), 2);

        match self.machine_st.try_from_list(self.machine_st.registers[1], stub_gen) {
            Err(e) => {
                return Err(e);
            }
            Ok(addrs) => {
                let string = self.machine_st.codes_to_string(addrs.into_iter(), stub_gen)?;
                self.machine_st.parse_number_from_string(string.as_str(), &self.indices, stub_gen)?;
            }
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn lifted_heap_length(&mut self) {
        let a1 = self.machine_st.registers[1];
        let lh_len = Fixnum::build_with(self.machine_st.lifted_heap.len() as i64);

        self.machine_st.unify_fixnum(lh_len, a1);
    }

    #[inline(always)]
    pub(crate) fn char_code(&mut self) -> CallResult {
        let stub_gen = || functor_stub(atom!("char_code"), 2);
        let a1 = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));

        let c = read_heap_cell!(a1,
            (HeapCellValueTag::Atom, (name, _arity)) => {
                name.as_char().unwrap()
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.machine_st.heap[s])
                    .get_name_and_arity();

                debug_assert_eq!(arity, 0);
                name.as_char().unwrap()
            }
            (HeapCellValueTag::Char, c) => {
                c
            }
            _ => {
                let a2 = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));

                match Number::try_from(a2) {
                    Ok(Number::Integer(n)) => {
                        let c = match n.to_u32().and_then(std::char::from_u32) {
                            Some(c) => c,
                            _ => {
                                let err = self.machine_st.representation_error(RepFlag::CharacterCode);
                                return Err(self.machine_st.error_form(err, stub_gen()));
                            }
                        };

                        self.machine_st.unify_char(c, a1);
                        return Ok(());
                    }
                    Ok(Number::Fixnum(n)) => {
                        match u32::try_from(n.get_num()) {
                            Ok(n) => {
                                if let Some(c) = std::char::from_u32(n) {
                                    self.machine_st.unify_char(c, a1);
                                    return Ok(());
                                }
                            }
                            _ => {}
                        }

                        let err = self.machine_st.representation_error(RepFlag::CharacterCode);
                        return Err(self.machine_st.error_form(err, stub_gen()));
                    }
                    _ => {
                        self.machine_st.fail = true;
                        return Ok(());
                    }
                }
            }
        );

        self.machine_st.unify_fixnum(
            Fixnum::build_with(c as i64),
            self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2])),
        );

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn char_type(&mut self) {
        let a1 = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
        let a2 = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));

        let c = read_heap_cell!(a1,
            (HeapCellValueTag::Char, c) => {
                c
            }
            (HeapCellValueTag::Atom, (name, _arity)) => {
                name.as_char().unwrap()
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.machine_st.heap[s])
                    .get_name_and_arity();

                debug_assert_eq!(arity, 0);
                name.as_char().unwrap()
            }
            _ => {
                unreachable!()
            }
        );

        let chars = cell_as_atom!(a2);
        self.machine_st.fail = true; // This predicate fails by default.

        macro_rules! macro_check {
            ($id:ident, $name:expr) => {
                if $id!(c) && chars == $name {
                    self.machine_st.fail = false;
                    return;
                }
            };
        }

        macro_rules! method_check {
            ($id:ident, $name:expr) => {
                if c.$id() && chars == $name {
                    self.machine_st.fail = false;
                    return;
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

    #[inline(always)]
    pub(crate) fn check_cut_point(&mut self) {
        let addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
        let old_b = cell_as_fixnum!(addr).get_num() as usize;

        let prev_b = self.machine_st.stack.index_or_frame(self.machine_st.b).prelude.b;
        let prev_b = self.machine_st.stack.index_or_frame(prev_b).prelude.b;

        if prev_b > old_b {
            self.machine_st.fail = true;
        }
    }

    #[inline(always)]
    pub(crate) fn copy_term_without_attr_vars(&mut self) {
        self.machine_st.copy_term(AttrVarPolicy::StripAttributes);
    }

    #[inline(always)]
    pub(crate) fn fetch_global_var(&mut self) {
        let key = cell_as_atom!(self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1])));
        let addr = self.machine_st.registers[2];

        match self.indices.global_variables.get_mut(&key) {
            Some((ref ball, ref mut loc)) => match loc {
                Some(value_loc) => {
                    unify_fn!(self.machine_st, addr, *value_loc);
                }
                None if !ball.stub.is_empty() => {
                    let h = self.machine_st.heap.len();
                    let stub = ball.copy_and_align(h);

                    self.machine_st.heap.extend(stub.into_iter());

                    unify_fn!(self.machine_st, addr, heap_loc_as_cell!(h));

                    if !self.machine_st.fail {
                        *loc = Some(heap_loc_as_cell!(h));
                        self.machine_st.trail(TrailRef::BlackboardEntry(key));
                    }
                }
                _ => self.machine_st.fail = true,
            },
            None => self.machine_st.fail = true,
        };
    }

    #[inline(always)]
    pub(crate) fn put_code(&mut self) -> CallResult {
        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices.stream_aliases,
            atom!("put_code"),
            2,
        )?;

        self.machine_st.check_stream_properties(
            stream,
            StreamType::Text,
            None,
            atom!("put_code"),
            2,
        )?;

        let stub_gen = || functor_stub(atom!("put_code"), 2);
        let addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));

        if addr.is_var() {
            let err = self.machine_st.instantiation_error();
            return Err(self.machine_st.error_form(err, stub_gen()));
        } else {
            match Number::try_from(addr) {
                Ok(Number::Integer(n)) => {
                    if let Some(c) = n.to_u32().and_then(|c| char::try_from(c).ok()) {
                        write!(&mut stream, "{}", c).unwrap();
                        return Ok(());
                    }
                }
                Ok(Number::Fixnum(n)) => {
                    let n = n.get_num();

                    if let Some(c) = u32::try_from(n).ok().and_then(|c| char::from_u32(c)) {
                        write!(&mut stream, "{}", c).unwrap();
                        return Ok(());
                    }
                }
                _ => {
                    let err = self.machine_st.type_error(ValidType::Integer, addr);
                    return Err(self.machine_st.error_form(err, stub_gen()));
                }
            }

            let err = self.machine_st.representation_error(RepFlag::CharacterCode);
            return Err(self.machine_st.error_form(err, stub_gen()));
        }
    }

    #[inline(always)]
    pub(crate) fn put_char(&mut self) -> CallResult {
        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices.stream_aliases,
            atom!("put_char"),
            2,
        )?;

        self.machine_st.check_stream_properties(
            stream,
            StreamType::Text,
            None,
            atom!("put_char"),
            2,
        )?;

        let stub_gen = || functor_stub(atom!("put_char"), 2);
        let addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));

        if addr.is_var() {
            let err = self.machine_st.instantiation_error();
            return Err(self.machine_st.error_form(err, stub_gen()));
        } else {
            read_heap_cell!(addr,
                (HeapCellValueTag::Atom, (name, _arity)) => {
                    let c = name.as_char().unwrap();
                    write!(&mut stream, "{}", c).unwrap();
                    return Ok(());
                }
                (HeapCellValueTag::Char, c) => {
                    write!(&mut stream, "{}", c).unwrap();
                    return Ok(());
                }
                _ => {
                }
            );

            let err = self.machine_st.type_error(ValidType::Character, addr);
            return Err(self.machine_st.error_form(err, stub_gen()));
        }
    }

    #[inline(always)]
    pub(crate) fn put_chars(&mut self) -> CallResult {
        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices.stream_aliases,
            atom!("$put_chars"),
            2,
        )?;

        let mut bytes = Vec::new();
        let stub_gen = || functor_stub(atom!("$put_chars"), 2);

        if let Some(string) = self.machine_st.value_to_str_like(self.machine_st.registers[2]) {
            if stream.options().stream_type() == StreamType::Binary {
                for c in string.as_str().chars() {
                    if c as u32 > 255 {
                        let err = self.machine_st.type_error(ValidType::Byte, char_as_cell!(c));
                        return Err(self.machine_st.error_form(err, stub_gen()));
                    }

                    bytes.push(c as u8);
                }
            } else {
                bytes = string.as_str().bytes().collect();
            }

            match stream.write_all(&bytes) {
                Ok(_) => {
                }
                _ => {
                    let addr = stream_as_cell!(stream);
                    let err = self.machine_st.existence_error(ExistenceError::Stream(addr));

                    return Err(self.machine_st.error_form(err, stub_gen()));
                }
            }
        } else {
            self.machine_st.fail = true;
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn put_byte(&mut self) -> CallResult {
        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices.stream_aliases,
            atom!("put_byte"),
            2,
        )?;

        self.machine_st.check_stream_properties(
            stream,
            StreamType::Binary,
            None,
            atom!("put_byte"),
            2,
        )?;

        let stub_gen = || functor_stub(atom!("put_byte"), 2);
        let addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));

        if addr.is_var() {
            let err = self.machine_st.instantiation_error();
            return Err(self.machine_st.error_form(err, stub_gen()));
        } else {
            match Number::try_from(addr) {
                Ok(Number::Integer(n)) => {
                    if let Some(nb) = n.to_u8() {
                        match stream.write(&mut [nb]) {
                            Ok(1) => {
                                return Ok(());
                            }
                            _ => {
                                let err = self.machine_st.existence_error(
                                    ExistenceError::Stream(stream_as_cell!(stream))
                                );

                                return Err(self.machine_st.error_form(err, stub_gen()));
                            }
                        }
                    }
                }
                Ok(Number::Fixnum(n)) => {
                    if let Ok(nb) = u8::try_from(n.get_num()) {
                        match stream.write(&mut [nb]) {
                            Ok(1) => {
                                return Ok(());
                            }
                            _ => {
                                let err = self.machine_st.existence_error(
                                    ExistenceError::Stream(stream_as_cell!(stream))
                                );

                                return Err(self.machine_st.error_form(err, stub_gen()));
                            }
                        }
                    }
                }
                _ => {
                }
            }
        }

        let err = self.machine_st.type_error(ValidType::Byte, self.machine_st.registers[2]);
        Err(self.machine_st.error_form(err, stub_gen()))
    }

    #[inline(always)]
    pub(crate) fn get_byte(&mut self) -> CallResult {
        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices.stream_aliases,
            atom!("get_byte"),
            2,
        )?;

        self.machine_st.check_stream_properties(
            stream,
            StreamType::Binary,
            Some(self.machine_st.registers[2]),
            atom!("get_byte"),
            2,
        )?;

        if stream.past_end_of_stream() {
            self.machine_st.eof_action(self.machine_st.registers[2], stream, atom!("get_byte"), 2)?;

            if EOFAction::Reset != stream.options().eof_action() {
                return Ok(());
            } else if self.machine_st.fail {
                return Ok(());
            }
        }

        let stub_gen = || functor_stub(atom!("get_byte"), 2);
        let addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));

        let addr = if addr.is_var() {
            addr
        } else {
            match Number::try_from(addr) {
                Ok(Number::Integer(n)) => {
                    if let Some(nb) = n.to_u8() {
                        fixnum_as_cell!(Fixnum::build_with(nb as i64))
                    } else {
                        let err = self.machine_st.type_error(ValidType::InByte, addr);
                        return Err(self.machine_st.error_form(err, stub_gen()));
                    }
                }
                Ok(Number::Fixnum(n)) => {
                    if let Ok(nb) = u8::try_from(n.get_num()) {
                        fixnum_as_cell!(Fixnum::build_with(nb as i64))
                    } else {
                        let err = self.machine_st.type_error(ValidType::InByte, addr);
                        return Err(self.machine_st.error_form(err, stub_gen()));
                    }
                }
                _ => {
                    let err = self.machine_st.type_error(ValidType::InByte, addr);
                    return Err(self.machine_st.error_form(err, stub_gen()));
                }
            }
        };

        loop {
            let mut b = [0u8; 1];

            match stream.read(&mut b) {
                Ok(1) => {
                    self.machine_st.unify_fixnum(Fixnum::build_with(b[0] as i64), addr);
                    break;
                }
                _ => {
                    stream.set_past_end_of_stream(true);
                    self.machine_st.unify_fixnum(Fixnum::build_with(-1), self.machine_st.registers[2]);
                    break;
                }
            }
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn get_char(&mut self) -> CallResult {
        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices.stream_aliases,
            atom!("get_char"),
            2,
        )?;

        self.machine_st.check_stream_properties(
            stream,
            StreamType::Text,
            Some(self.machine_st.registers[2]),
            atom!("get_char"),
            2,
        )?;

        if stream.past_end_of_stream() {
            if EOFAction::Reset != stream.options().eof_action() {
                return Ok(());
            } else if self.machine_st.fail {
                return Ok(());
            }
        }

        if stream.at_end_of_stream() {
            let end_of_file = atom!("end_of_file");
            stream.set_past_end_of_stream(true);

            self.machine_st.unify_atom(
                end_of_file,
                self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]))
            );

            return Ok(());
        }

        let stub_gen = || functor_stub(atom!("get_char"), 2);
        let mut iter = self.machine_st.open_parsing_stream(stream, atom!("get_char"), 2)?;

        let addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));

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
                    let err = self.machine_st.type_error(ValidType::InCharacter, addr);
                    return Err(self.machine_st.error_form(err, stub_gen()));
                }
            )
        };

        loop {
            let result = iter.read_char();

            match result {
                Some(Ok(c)) => {
                    self.machine_st.unify_char(c, addr);
                    break;
                }
                _ => {
                    self.machine_st.eof_action(
                        self.machine_st.registers[2],
                        stream,
                        atom!("get_char"),
                        2,
                    )?;

                    if EOFAction::Reset != stream.options().eof_action() {
                        break;
                    } else if self.machine_st.fail {
                        break;
                    }
                }
            }
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn get_n_chars(&mut self) -> CallResult {
        let stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices.stream_aliases,
            atom!("get_n_chars"),
            3,
        )?;

        let num = match Number::try_from(self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]))) {
            Ok(Number::Fixnum(n)) => usize::try_from(n.get_num()).unwrap(),
            Ok(Number::Integer(n)) => match n.to_usize() {
                Some(u) => u,
                _ => {
                    self.machine_st.fail = true;
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
            let mut iter = self.machine_st.open_parsing_stream(stream, atom!("get_n_chars"), 2)?;

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

        let output = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[3]));
        let atom = self.machine_st.atom_tbl.build_with(&string);

        self.machine_st.unify_complete_string(atom, output);
        Ok(())
    }

    #[inline(always)]
    pub(crate) fn get_code(&mut self) -> CallResult {
        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices.stream_aliases,
            atom!("get_code"),
            2,
        )?;

        self.machine_st.check_stream_properties(
            stream,
            StreamType::Text,
            Some(self.machine_st.registers[2]),
            atom!("get_code"),
            2,
        )?;

        if stream.past_end_of_stream() {
            if EOFAction::Reset != stream.options().eof_action() {
                return Ok(());
            } else if self.machine_st.fail {
                return Ok(());
            }
        }

        if stream.at_end_of_stream() {
            let end_of_file = atom!("end_of_file");
            stream.set_past_end_of_stream(true);

            self.machine_st.unify_atom(
                end_of_file,
                self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2])),
            );

            return Ok(());
        }

        let stub_gen = || functor_stub(atom!("get_code"), 2);
        let addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));

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
                        let err = self.machine_st.representation_error(RepFlag::InCharacterCode);
                        return Err(self.machine_st.error_form(err, stub_gen()));
                    }
                }
                Ok(Number::Fixnum(n)) => {
                    let nf = u32::try_from(n.get_num())
                        .ok()
                        .and_then(|n| std::char::from_u32(n));

                    if nf.is_some() {
                        fixnum_as_cell!(n)
                    } else {
                        let err = self.machine_st.representation_error(RepFlag::InCharacterCode);
                        return Err(self.machine_st.error_form(err, stub_gen()));
                    }
                }
                _ => {
                    let err = self.machine_st.type_error(ValidType::Integer, self.machine_st.registers[2]);
                    return Err(self.machine_st.error_form(err, stub_gen()));
                }
            }
        };

        let mut iter = self.machine_st.open_parsing_stream(stream.clone(), atom!("get_code"), 2)?;

        loop {
            let result = iter.read_char();

            match result {
                Some(Ok(c)) => {
                    self.machine_st.unify_fixnum(Fixnum::build_with(c as i64), addr);
                    break;
                }
                _ => {
                    self.machine_st.eof_action(
                        self.machine_st.registers[2],
                        stream,
                        atom!("get_code"),
                        2,
                    )?;

                    if EOFAction::Reset != stream.options().eof_action() {
                        break;
                    } else if self.machine_st.fail {
                        break;
                    }
                }
            }
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn first_stream(&mut self) {
        let mut first_stream = None;
        let mut null_streams = BTreeSet::new();

        for stream in self.indices.streams.iter().cloned() {
            if !stream.is_null_stream() {
                first_stream = Some(stream);
                break;
            } else {
                null_streams.insert(stream);
            }
        }

        self.indices.streams = self.indices.streams.sub(&null_streams);

        if let Some(first_stream) = first_stream {
            let stream = stream_as_cell!(first_stream);

            let var = self.machine_st.store(self.machine_st.deref(
                self.machine_st.registers[1]
            )).as_var().unwrap();

            self.machine_st.bind(var, stream);
        } else {
            self.machine_st.fail = true;
        }
    }

    #[inline(always)]
    pub(crate) fn next_stream(&mut self) {
        let prev_stream = cell_as_stream!(self.machine_st.store(self.machine_st.deref(
            self.machine_st.registers[1]
        )));

        let mut next_stream = None;
        let mut null_streams = BTreeSet::new();

        for stream in self.indices
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

        self.indices.streams = self.indices.streams.sub(&null_streams);

        if let Some(next_stream) = next_stream {
            let var = self.machine_st.store(self.machine_st.deref(
                self.machine_st.registers[2]
            )).as_var().unwrap();

            let next_stream = stream_as_cell!(next_stream);
            self.machine_st.bind(var, next_stream);
        } else {
            self.machine_st.fail = true;
        }
    }

    #[inline(always)]
    pub(crate) fn flush_output(&mut self) -> CallResult {
        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices.stream_aliases,
            atom!("flush_output"),
            1,
        )?;

        if !stream.is_output_stream() {
            let stub = functor_stub(atom!("flush_output"), 1);
            let addr = stream_as_cell!(stream);

            let err = self.machine_st.permission_error(
                Permission::OutputStream,
                atom!("stream"),
                addr,
            );

            return Err(self.machine_st.error_form(err, stub));
        }

        stream.flush().unwrap();
        Ok(())
    }

    #[inline(always)]
    pub(crate) fn get_single_char(&mut self) -> CallResult {
        let ctrl_c = KeyEvent {
            code: KeyCode::Char('c'),
            modifiers: KeyModifiers::CONTROL,
        };

        let key = get_key();

        if key == ctrl_c {
            let stub = functor_stub(atom!("get_single_char"), 1);
            let err = self.machine_st.interrupt_error();
            let err = self.machine_st.error_form(err, stub);

            return Err(err);
        }

        let c = match key.code {
            KeyCode::Enter => '\n',
            KeyCode::Tab => '\t',
            KeyCode::Char(c) => c,
            _ => unreachable!(),
        };

        self.machine_st.unify_char(
            c,
            self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1])),
        );

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn head_is_dynamic(&mut self) {
        let module_name = cell_as_atom!(self.machine_st.store(self.machine_st.deref(
            self.machine_st.registers[1])
        ));

        let (name, arity) = read_heap_cell!(
            self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2])),
            (HeapCellValueTag::Str, s) => {
                cell_as_atom_cell!(self.machine_st.heap[s]).get_name_and_arity()
            }
            (HeapCellValueTag::Atom, (name, _arity)) => {
                (name, 0)
            }
            _ => {
                unreachable!()
            }
        );

        self.machine_st.fail = !self.indices.is_dynamic_predicate(module_name, (name, arity));
    }

    #[inline(always)]
    pub(crate) fn close(&mut self) -> CallResult {
        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices.stream_aliases,
            atom!("close"),
            2,
        )?;

        if !stream.is_input_stream() {
            stream.flush().unwrap(); // 8.11.6.1b)
        }

        self.indices.streams.remove(&stream);

        if stream == self.user_input {
            self.user_input = self.indices
                .stream_aliases
                .get(&atom!("user_input"))
                .cloned()
                .unwrap();

            self.indices.streams.insert(self.user_input);
        } else if stream == self.user_output {
            self.user_output = self.indices
                .stream_aliases
                .get(&atom!("user_output"))
                .cloned()
                .unwrap();

            self.indices.streams.insert(self.user_output);
        }

        if !stream.is_stdin() && !stream.is_stdout() && !stream.is_stderr() {
            if let Some(alias) = stream.options().get_alias() {
                self.indices.stream_aliases.remove(&alias);
            }

            let close_result = stream.close();

            if let Err(_) = close_result {
                let stub = functor_stub(atom!("close"), 1);
                let addr = stream_as_cell!(stream);
                let err  = self.machine_st.existence_error(ExistenceError::Stream(addr));

                return Err(self.machine_st.error_form(err, stub));
            }
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn copy_to_lifted_heap(&mut self) {
        let lh_offset = cell_as_fixnum!(
            self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]))
        ).get_num() as usize;

        let copy_target = self.machine_st.registers[2];

        let old_threshold = self.machine_st.copy_findall_solution(lh_offset, copy_target);
        let new_threshold = self.machine_st.lifted_heap.len() - lh_offset;

        self.machine_st.lifted_heap[old_threshold] = heap_loc_as_cell!(new_threshold);

        for addr in self.machine_st.lifted_heap[old_threshold + 1 ..].iter_mut() {
            *addr -= self.machine_st.heap.len() + lh_offset;
        }
    }

    #[inline(always)]
    pub(crate) fn delete_attribute(&mut self) {
        let ls0 = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));

        if let HeapCellValueTag::Lis = ls0.get_tag() {
            let l1 = ls0.get_value();
            let ls1 = self.machine_st.store(self.machine_st.deref(heap_loc_as_cell!(l1 + 1)));

            if let HeapCellValueTag::Lis = ls1.get_tag() {
                let l2 = ls1.get_value();

                let old_addr = self.machine_st.store(self.machine_st.deref(self.machine_st.heap[l1+1]));
                let tail = self.machine_st.store(self.machine_st.deref(heap_loc_as_cell!(l2 + 1)));

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

                self.machine_st.heap[l1 + 1] = tail;
                self.machine_st.trail(trail_ref);
            }
        }
    }

    #[inline(always)]
     pub(crate) fn delete_head_attribute(&mut self) {
        let addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));

        debug_assert_eq!(addr.get_tag(), HeapCellValueTag::AttrVar);

        let h = addr.get_value();
        let addr = self.machine_st.store(self.machine_st.deref(self.machine_st.heap[h + 1]));

        debug_assert_eq!(addr.get_tag(), HeapCellValueTag::Lis);

        let l = addr.get_value();
        let tail = self.machine_st.store(self.machine_st.deref(self.machine_st.heap[l + 1]));

        let tail = if tail.is_var() {
            self.machine_st.heap[h] = heap_loc_as_cell!(h);
            self.machine_st.trail(TrailRef::Ref(Ref::attr_var(h)));

            heap_loc_as_cell!(h + 1)
        } else {
            tail
        };

        self.machine_st.heap[h + 1] = tail;
        self.machine_st.trail(TrailRef::AttrVarListLink(h + 1, l));
    }

    #[inline(always)]
    pub(crate) fn dynamic_module_resolution(
        &mut self,
        narity: usize,
    ) -> Result<(Atom, PredicateKey), MachineStub> {
        let module_name = self.machine_st.store(self.machine_st.deref(
            self.machine_st.registers[1]
        ));

        let module_name = read_heap_cell!(module_name,
            (HeapCellValueTag::Atom, (name, _arity)) => {
                debug_assert_eq!(_arity, 0);
                name
            }
            (HeapCellValueTag::Str, s) => {
                let (module_name, _arity) = cell_as_atom_cell!(self.machine_st.heap[s])
                    .get_name_and_arity();

                debug_assert_eq!(_arity, 0);
                module_name
            }
            _ if module_name.is_var() => {
                atom!("user")
            }
            _ => {
                unreachable!()
            }
        );

        let goal = self.machine_st.store(self.machine_st.deref(
            self.machine_st.registers[2]
        ));

        let (name, arity, s) = self.machine_st.setup_call_n_init_goal_info(goal, narity)?;

        match arity.cmp(&2) {
            Ordering::Less => {
                for i in arity + 1..arity + narity + 1 {
                    self.machine_st.registers[i] = self.machine_st.registers[i + 2 - arity];
                }
            }
            Ordering::Greater => {
                for i in (arity + 1..arity + narity + 1).rev() {
                    self.machine_st.registers[i] = self.machine_st.registers[i + 2 - arity];
                }
            }
            Ordering::Equal => {}
        }

        let key = (name, arity + narity);

        for i in 1..arity + 1 {
            self.machine_st.registers[i] = self.machine_st.heap[s + i];
        }

        Ok((module_name, key))
    }

    #[inline(always)]
    pub(crate) fn enqueue_attributed_var(&mut self) {
        let addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));

        read_heap_cell!(addr,
            (HeapCellValueTag::AttrVar, h) => {
                self.machine_st.attr_var_init.attr_var_queue.push(h);
            }
            _ => {
            }
        );
    }

    #[inline(always)]
    pub(crate) fn get_next_db_ref(&mut self) {
        let a1 = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));

        if let Some(name_var) = a1.as_var() {
            let mut iter = self.indices.code_dir.iter();

            while let Some(((name, arity), _)) = iter.next() {
                let arity_var = self.machine_st.deref(self.machine_st.registers[2])
                    .as_var().unwrap();

                self.machine_st.bind(name_var, atom_as_cell!(name));
                self.machine_st.bind(arity_var, fixnum_as_cell!(Fixnum::build_with(*arity as i64)));

                return;
            }

            self.machine_st.fail = true;
        } else if a1.get_tag() == HeapCellValueTag::Atom {
            let name = cell_as_atom!(a1);
            let arity = cell_as_fixnum!(self.machine_st.store(self.machine_st.deref(
                self.machine_st.registers[2])
            )).get_num() as usize;

            match self.machine_st.get_next_db_ref(&self.indices, &DBRef::NamedPred(name, arity)) {
                Some(DBRef::NamedPred(name, arity)) => {
                    let atom_var = self.machine_st.deref(self.machine_st.registers[3])
                        .as_var().unwrap();

                    let arity_var = self.machine_st.deref(self.machine_st.registers[4])
                        .as_var().unwrap();

                    self.machine_st.bind(atom_var, atom_as_cell!(name));
                    self.machine_st.bind(arity_var, fixnum_as_cell!(Fixnum::build_with(arity as i64)));
                }
                Some(DBRef::Op(..)) | None => {
                    self.machine_st.fail = true;
                }
            }
        } else {
            self.machine_st.fail = true;
        }
    }

    #[inline(always)]
    pub(crate) fn get_next_op_db_ref(&mut self) {
        let prec = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));

        if let Some(prec_var) = prec.as_var() {
            let spec = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));
            let op = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[3]));
            let orig_op = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[7]));

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
                let orig_op = read_heap_cell!(orig_op,
                    (HeapCellValueTag::Atom, (name, _arity)) => {
                        name
                    }
                    (HeapCellValueTag::Str, s) => {
                        cell_as_atom!(self.machine_st.heap[s])
                    }
                    (HeapCellValueTag::Char, c) => {
                        self.machine_st.atom_tbl.build_with(&c.to_string())
                    }
                    _ => {
                        unreachable!()
                    }
                );

                let op_descs = [
                    self.indices.op_dir.get_key_value(&(orig_op, Fixity::In)),
                    self.indices.op_dir.get_key_value(&(orig_op, Fixity::Pre)),
                    self.indices.op_dir.get_key_value(&(orig_op, Fixity::Post)),
                ];

                let number_of_keys = op_descs[0].is_some() as usize +
                    op_descs[1].is_some() as usize +
                    op_descs[2].is_some() as usize;

                match number_of_keys {
                    0 => {
                        self.machine_st.fail = true;
                        return;
                    }
                    1 => {
                        for op_desc in op_descs {
                            if let Some((_, op_desc)) = op_desc {
                                let (op_prec, op_spec) =
                                    (op_desc.get_prec(), op_desc.get_spec());

                                if op_prec == 0 {
                                    // 8.14.4, note 2
                                    self.machine_st.fail = true;
                                    return;
                                }

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

                                self.machine_st.unify_fixnum(op_prec, prec);
                                self.machine_st.unify_atom(op_spec, spec);
                            }
                        }

                        return;
                    }
                    _ => {
                        let mut unossified_op_dir = OssifiedOpDir::new();

                        for op_desc in op_descs {
                            if let Some((key, op_desc)) = op_desc {
                                let (prec, spec) = (op_desc.get_prec(), op_desc.get_spec());

                                if prec == 0 {
                                    // 8.14.4, note 2
                                    continue;
                                }

                                unossified_op_dir.insert(*key, (prec as usize, spec as Specifier));
                            }
                        }

                        unossified_op_dir
                    }
                }
            } else {
                let mut unossified_op_dir = OssifiedOpDir::new();

                unossified_op_dir.extend(self.indices.op_dir.iter().filter_map(
                    |(key, op_desc)| {
                        let (other_prec, other_spec) = (op_desc.get_prec(), op_desc.get_spec());
                        let name = key.0;

                        if other_prec == 0 {
                            // 8.14.4, note 2
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

            let ossified_op_dir = arena_alloc!(unossified_op_dir, &mut self.machine_st.arena);

            match ossified_op_dir.iter().next() {
                Some(((op_atom, _), (op_prec, op_spec))) => {
                    let ossified_op_dir_var = self.machine_st.store(self.machine_st.deref(
                        self.machine_st.registers[4]
                    )).as_var().unwrap();

                    let spec_atom = match *op_spec {
                        FX => atom!("fx"),
                        FY => atom!("fy"),
                        XF => atom!("xf"),
                        YF => atom!("yf"),
                        XFX => atom!("xfx"),
                        XFY => atom!("xfy"),
                        YFX => atom!("yfx"),
                        _ => {
                            self.machine_st.fail = true;
                            return;
                        }
                    };

                    let spec_var = spec.as_var().unwrap();
                    let op_var = op.as_var().unwrap();

                    self.machine_st.bind(prec_var, fixnum_as_cell!(Fixnum::build_with(*op_prec as i64)));
                    self.machine_st.bind(spec_var, atom_as_cell!(spec_atom));
                    self.machine_st.bind(op_var, atom_as_cell!(op_atom));
                    self.machine_st.bind(ossified_op_dir_var, typed_arena_ptr_as_cell!(ossified_op_dir));
                }
                None => {
                    self.machine_st.fail = true;
                    return;
                }
            }
        } else {
            let spec = cell_as_atom!(self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2])));
            let op_atom = cell_as_atom!(self.machine_st.store(self.machine_st.deref(self.machine_st.registers[3])));
            let ossified_op_dir_cell = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[4]));

            if ossified_op_dir_cell.is_var() {
                self.machine_st.fail = true;
                return;
            }

            let ossified_op_dir = cell_as_ossified_op_dir!(
                ossified_op_dir_cell
            );

            let fixity = match spec {
                atom!("xfy") | atom!("yfx") | atom!("xfx") => Fixity::In,
                atom!("xf") | atom!("yf") => Fixity::Post,
                atom!("fx") | atom!("fy") => Fixity::Pre,
                _ => {
                    self.machine_st.fail = true;
                    return;
                }
            };

            match self.machine_st.get_next_db_ref(
                &self.indices,
                &DBRef::Op(op_atom, fixity, ossified_op_dir),
            ) {
                Some(DBRef::Op(op_atom, fixity, ossified_op_dir)) => {
                    let (prec, spec) = ossified_op_dir.get(&(op_atom, fixity)).unwrap();

                    let prec_var = self.machine_st.deref(self.machine_st.registers[5])
                        .as_var().unwrap();

                    let spec_var = self.machine_st.deref(self.machine_st.registers[6])
                        .as_var().unwrap();

                    let op_var = self.machine_st.deref(self.machine_st.registers[7])
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
                            self.machine_st.fail = true;
                            return;
                        }
                    };

                    self.machine_st.bind(prec_var, fixnum_as_cell!(Fixnum::build_with(*prec as i64)));
                    self.machine_st.bind(spec_var, atom_as_cell!(spec_atom));
                    self.machine_st.bind(op_var, atom_as_cell!(op_atom));
                }
                Some(DBRef::NamedPred(..)) | None => {
                    self.machine_st.fail = true;
                }
            }
        }
    }

    #[inline(always)]
    pub(crate) fn maybe(&mut self) {
        let result = {
            let mut rand = RANDOM_STATE.borrow_mut();
            rand.bits(1) == 0
        };

        self.machine_st.fail = result;
    }

    #[inline(always)]
    pub(crate) fn cpu_now(&mut self) {
        let secs = ProcessTime::now().as_duration().as_secs_f64();
        let secs = float_alloc!(secs, self.machine_st.arena);

        self.machine_st.unify_f64(secs, self.machine_st.registers[1]);
    }

    #[inline(always)]
    pub(crate) fn det_length_rundown(&mut self) -> CallResult {
        let stub_gen = || functor_stub(atom!("length"), 2);
        let len = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));

        let n = match Number::try_from(len) {
            Ok(Number::Fixnum(n)) => n.get_num() as usize,
            Ok(Number::Integer(n)) => match n.to_usize() {
                Some(n) => n,
                None => {
                    let err = self.machine_st.resource_error(len);
                    return Err(self.machine_st.error_form(err, stub_gen()));
                }
            }
            _ => {
                unreachable!()
            }
        };

        let h = self.machine_st.heap.len();

        iter_to_heap_list(
            &mut self.machine_st.heap,
            (0 .. n).map(|i| heap_loc_as_cell!(h + 2 * i + 1)),
        );

        let tail = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
        self.machine_st.bind(tail.as_var().unwrap(), heap_loc_as_cell!(h));

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn http_open(&mut self) -> CallResult {
        let address_sink = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
        let method =  read_heap_cell!(self.machine_st.store(self.machine_st.deref(self.machine_st.registers[3])),
            (HeapCellValueTag::Atom, (name, arity)) => {
                debug_assert_eq!(arity, 0);
                match name {
                    atom!("get") => Method::GET,
                    atom!("post") => Method::POST,
                    atom!("put") => Method::PUT,
                    atom!("delete") => Method::DELETE,
                    atom!("patch") => Method::PATCH,
                    atom!("head") => Method::HEAD,
                    _ => unreachable!(),
                }
            }
            _ => {
                unreachable!()
            }
        );
        let address_status = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[4]));
        let address_data = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[5]));
        let mut bytes: Vec<u8> = Vec::new();
        if let Some(string) = self.machine_st.value_to_str_like(address_data) {
            bytes = string.as_str().bytes().collect();
        }
        let stub_gen = || functor_stub(atom!("http_open"), 3);

        let headers = match self.machine_st.try_from_list(self.machine_st.registers[7], stub_gen) {
            Ok(addrs) => {
                let mut header_map = HeaderMap::new();
                for heap_cell in addrs{
                   read_heap_cell!(heap_cell,
                       (HeapCellValueTag::Str, s) => {
                           let name = cell_as_atom_cell!(self.machine_st.heap[s]).get_name();
                           let value = self.machine_st.value_to_str_like(self.machine_st.heap[s + 1]).unwrap();
                           header_map.insert(HeaderName::from_str(name.as_str()).unwrap(), HeaderValue::from_str(value.as_str()).unwrap());
                       }
                       _ => {
                           unreachable!()
                       }
                   )
                }
                header_map
            },
            Err(e) => return Err(e)
        };
        if let Some(address_sink) = self.machine_st.value_to_str_like(address_sink) {
            let address_string = address_sink.as_str(); //to_string();
            let address: Uri = address_string.parse().unwrap();

            let stream = self.runtime.block_on(async {
                let https = HttpsConnector::new();
                let client = Client::builder()
                    .build::<_, hyper::Body>(https);

                // request
                let mut req = Request::builder()
                    .method(method)
                    .uri(address)
                    .body(Body::from(bytes))
                    .unwrap();
                // request headers
                *req.headers_mut() = headers;
                // do it!
                let resp = client.request(req).await.unwrap();
                // status code
                let status = resp.status().as_u16();
                self.machine_st.unify_fixnum(Fixnum::build_with(status as i64), address_status);
                // headers
                let headers: Vec<HeapCellValue> = resp.headers().iter().map(|(header_name, header_value)| {
                    let h = self.machine_st.heap.len();

                    let header_term = functor!(
                        self.machine_st.atom_tbl.build_with(header_name.as_str()),
                        [cell(string_as_cstr_cell!(self.machine_st.atom_tbl.build_with(header_value.to_str().unwrap())))]
                    );

                    self.machine_st.heap.extend(header_term.into_iter());
                    str_loc_as_cell!(h)
                }).collect();

                let headers_list = iter_to_heap_list(&mut self.machine_st.heap, headers.into_iter());
                unify!(self.machine_st, heap_loc_as_cell!(headers_list), self.machine_st.registers[6]);
                // body
                let buf = hyper::body::aggregate(resp).await.unwrap();
                let reader = buf.reader();

                let mut stream = Stream::from_http_stream(
                    self.machine_st.atom_tbl.build_with(&address_string),
                    Box::new(reader),
                    &mut self.machine_st.arena
                );
                *stream.options_mut() = StreamOptions::default();
                if let Some(alias) = stream.options().get_alias() {
                    self.indices.stream_aliases.insert(alias, stream);
                }

                self.indices.streams.insert(stream);

                stream_as_cell!(stream)
            });

            let stream_addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));
            self.machine_st.bind(stream_addr.as_var().unwrap(), stream);

        } else {
            let err = self.machine_st.domain_error(DomainErrorType::SourceSink, address_sink);
            let stub = functor_stub(atom!("http_open"), 3);

            return Err(self.machine_st.error_form(err, stub));
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn http_listen(&mut self) -> CallResult {
	let address_sink = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
	if let Some(address_str) = self.machine_st.value_to_str_like(address_sink) {
	    let address_string = address_str.as_str();
	    let addr: SocketAddr = match address_string.to_socket_addrs().ok().and_then(|mut s| s.next()) {
		Some(addr) => addr,
                _ => {
                    self.machine_st.fail = true;
                    return Ok(());
                }
	    };

	    let (tx, rx) = channel(1);
	    let tx = Arc::new(Mutex::new(tx));

	    let _guard = self.runtime.enter();
	    let server = match Server::try_bind(&addr) {
		Ok(server) => server,
		Err(_) => {
		    return Err(self.machine_st.open_permission_error(address_sink, atom!("http_listen"), 2));
		}
	    };

	    self.runtime.spawn(async move {
		let make_svc = make_service_fn(move |_conn| {
		    let tx = tx.clone();
		    async move { Ok::<_, Infallible>(service_fn(move |req| http::serve_req(req, tx.clone()))) }
		});
		let server = server.serve(make_svc);

		if let Err(_) = server.await {
		    eprintln!("server error");
		}
	    });
	    let http_listener = HttpListener { incoming: rx };
	    let http_listener = arena_alloc!(http_listener, &mut self.machine_st.arena);
	    let addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));
	    self.machine_st.bind(addr.as_var().unwrap(), typed_arena_ptr_as_cell!(http_listener));
	}
	Ok(())
    }

    #[inline(always)]
    pub(crate) fn http_accept(&mut self) -> CallResult {
	let culprit = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
	let method = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));
	let path = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[3]));
	let query = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[5]));
	let stream_addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[6]));
	let handle_addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[7]));
	read_heap_cell!(culprit,
	    (HeapCellValueTag::Cons, cons_ptr) => {
		match_untyped_arena_ptr!(cons_ptr,
		    (ArenaHeaderTag::HttpListener, http_listener) => {
		        match http_listener.incoming.blocking_recv() {
			    Some(request) => {
			        let method_atom = match *request.request.method() {
				    Method::GET => atom!("get"),
				    Method::POST => atom!("post"),
				    Method::PUT => atom!("put"),
				    Method::DELETE => atom!("delete"),
				    Method::PATCH => atom!("patch"),
				    Method::HEAD => atom!("head"),
				    _ => unreachable!(),
				};
				let path_atom = self.machine_st.atom_tbl.build_with(request.request.uri().path());
				let path_cell = atom_as_cstr_cell!(path_atom);
				let headers: Vec<HeapCellValue> = request.request.headers().iter().map(|(header_name, header_value)| {
				    let h = self.machine_st.heap.len();

				    let header_term = functor!(
				        self.machine_st.atom_tbl.build_with(header_name.as_str()),
					[cell(string_as_cstr_cell!(self.machine_st.atom_tbl.build_with(header_value.to_str().unwrap())))]
				    );

				    self.machine_st.heap.extend(header_term.into_iter());
				    str_loc_as_cell!(h)
				}).collect();

				let headers_list = iter_to_heap_list(&mut self.machine_st.heap, headers.into_iter());

				let query_str = request.request.uri().query().unwrap_or("");
				let query_atom = self.machine_st.atom_tbl.build_with(query_str);
				let query_cell = string_as_cstr_cell!(query_atom);
				
				let hyper_req = request.request;
				let buf = self.runtime.block_on(async {hyper::body::aggregate(hyper_req).await.unwrap()});
				let reader = buf.reader();

				let mut stream = Stream::from_http_stream(
				    path_atom,
				    Box::new(reader),
				    &mut self.machine_st.arena
				);
				*stream.options_mut() = StreamOptions::default();
				stream.options_mut().set_stream_type(StreamType::Binary);
				self.indices.streams.insert(stream);
				let stream = stream_as_cell!(stream);

				let handle = arena_alloc!(request.response, &mut self.machine_st.arena);

				self.machine_st.bind(method.as_var().unwrap(), atom_as_cell!(method_atom));
				self.machine_st.bind(path.as_var().unwrap(), path_cell);
				unify!(self.machine_st, heap_loc_as_cell!(headers_list), self.machine_st.registers[4]);
				self.machine_st.bind(query.as_var().unwrap(), query_cell);
				self.machine_st.bind(stream_addr.as_var().unwrap(), stream);
				self.machine_st.bind(handle_addr.as_var().unwrap(), typed_arena_ptr_as_cell!(handle));
				}
			    None => {
			        self.machine_st.fail = true;
			    }
			}
		    }
		    _ => {
		        unreachable!();
		    }
		);
	    }
	    _ => {
	        unreachable!();
	    }
	);
	Ok(())
    }

    #[inline(always)]
    pub(crate) fn http_answer(&mut self) -> CallResult {
	let culprit = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
	let status_code = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));
	let status_code: u16 = match Number::try_from(status_code) {
	    Ok(Number::Fixnum(n)) => n.get_num() as u16,
	    Ok(Number::Integer(n)) => match n.to_u16() {
		Some(u) => u,
		_ => {
		    self.machine_st.fail = true;
		    return Ok(());
		}
	    }
	    _ => unreachable!()
	};
	let stub_gen = || functor_stub(atom!("http_listen"), 2);
	let headers = match self.machine_st.try_from_list(self.machine_st.registers[3], stub_gen) {
            Ok(addrs) => {
                let mut header_map = HeaderMap::new();
                for heap_cell in addrs{
                   read_heap_cell!(heap_cell,
                       (HeapCellValueTag::Str, s) => {
                           let name = cell_as_atom_cell!(self.machine_st.heap[s]).get_name();
                           let value = self.machine_st.value_to_str_like(self.machine_st.heap[s + 1]).unwrap();
                           header_map.insert(HeaderName::from_str(name.as_str()).unwrap(), HeaderValue::from_str(value.as_str()).unwrap());
                       }
                       _ => {
                           unreachable!()
                       }
                   )
                }
                header_map
            },
            Err(e) => return Err(e)
        };
	let stream_addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[4]));

	read_heap_cell!(culprit,
	    (HeapCellValueTag::Cons, cons_ptr) => {
		match_untyped_arena_ptr!(cons_ptr,
		    (ArenaHeaderTag::HttpResponse, http_response) => {
			let mut response = Response::builder()
			    .status(status_code);
			*response.headers_mut().unwrap() = headers;
			let (sender, body) = Body::channel();
			let response = response.body(body).unwrap();
			http_response.blocking_send(response).unwrap();

			let mut stream = Stream::from_http_sender(
			    sender,
			    &mut self.machine_st.arena
			);
			*stream.options_mut() = StreamOptions::default();
			stream.options_mut().set_stream_type(StreamType::Binary);
			self.indices.streams.insert(stream);
			let stream = stream_as_cell!(stream);
			self.machine_st.bind(stream_addr.as_var().unwrap(), stream);
		    }
		    _ => {
			unreachable!();
		    }
		);
	    }
	    _ => {
		unreachable!();
	    }
	);

	Ok(())
    }

    #[inline(always)]
    pub(crate) fn current_time(&mut self) {
        let timestamp = self.systemtime_to_timestamp(SystemTime::now());
        self.machine_st.unify_complete_string(timestamp, self.machine_st.registers[1]);
    }

    #[inline(always)]
    pub(crate) fn open(&mut self) -> CallResult {
        let alias = self.machine_st.registers[4];
        let eof_action = self.machine_st.registers[5];
        let reposition = self.machine_st.registers[6];
        let stream_type = self.machine_st.registers[7];

        let options  = self.machine_st.to_stream_options(alias, eof_action, reposition, stream_type);
        let src_sink = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));

        if let Some(file_spec) = self.machine_st.value_to_str_like(src_sink) {
            let file_spec = file_spec.as_atom(&mut self.machine_st.atom_tbl);

            let mut stream = self.machine_st.stream_from_file_spec(
                file_spec,
                &mut self.indices,
                &options,
            )?;

            *stream.options_mut() = options;
            self.indices.streams.insert(stream);

            if let Some(alias) = stream.options().get_alias() {
                self.indices.stream_aliases.insert(alias, stream);
            }

            let stream_var = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[3]));
            self.machine_st.bind(stream_var.as_var().unwrap(), stream_as_cell!(stream));
        } else {
            let err = self.machine_st.domain_error(DomainErrorType::SourceSink, src_sink);
            let stub = functor_stub(atom!("open"), 4);

            return Err(self.machine_st.error_form(err, stub));
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn op_declaration(&mut self) -> CallResult {
        let priority = self.machine_st.registers[1];
        let specifier = self.machine_st.registers[2];
        let op = self.machine_st.registers[3];

        let priority = self.machine_st.store(self.machine_st.deref(priority));

        let priority = match Number::try_from(priority) {
            Ok(Number::Integer(n)) => n.to_u16().unwrap(),
            Ok(Number::Fixnum(n)) => u16::try_from(n.get_num()).unwrap(),
            _ => {
                unreachable!();
            }
        };

        let specifier = cell_as_atom_cell!(self.machine_st.store(self.machine_st.deref(specifier)))
            .get_name();

        let op = read_heap_cell!(self.machine_st.store(self.machine_st.deref(op)),
            (HeapCellValueTag::Char, c) => {
                self.machine_st.atom_tbl.build_with(&c.to_string())
            }
            (HeapCellValueTag::Atom, (name, _arity)) => {
                name
            }
            (HeapCellValueTag::Str, s) => {
                cell_as_atom!(self.machine_st.heap[s])
            }
            _ => {
                unreachable!()
            }
        );

        let result = to_op_decl(priority, specifier, op)
            .map_err(SessionError::from)
            .and_then(|mut op_decl| {
                if op_decl.op_desc.get_prec() == 0 {
                    Ok(op_decl.remove(&mut self.indices.op_dir))
                } else {
                    let spec = get_op_desc(
                        op_decl.name,
                        &CompositeOpDir::new(&self.indices.op_dir, None),
                    );

                    op_decl.submit(spec, &mut self.indices.op_dir)
                }
            });

        match result {
            Ok(()) => Ok(()),
            Err(e) => {
                // 8.14.3.3 l)
                let err = self.machine_st.session_error(e);
                let stub = functor_stub(atom!("op"), 3);

                Err(self.machine_st.error_form(err, stub))
            }
        }
    }

    #[inline(always)]
    pub(crate) fn set_stream_options(&mut self) -> CallResult {
        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices.stream_aliases,
            atom!("open"),
            4,
        )?;

        let alias = self.machine_st.registers[2];
        let eof_action = self.machine_st.registers[3];
        let reposition = self.machine_st.registers[4];
        let stream_type = self.machine_st.registers[5];

        let options = self.machine_st.to_stream_options(alias, eof_action, reposition, stream_type);
        *stream.options_mut() = options;

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn truncate_if_no_lifted_heap_growth_diff(&mut self) {
        self.machine_st.truncate_if_no_lifted_heap_diff(|h| heap_loc_as_cell!(h))
    }

    #[inline(always)]
    pub(crate) fn truncate_if_no_lifted_heap_growth(&mut self) {
        self.machine_st.truncate_if_no_lifted_heap_diff(|_| empty_list_as_cell!())
    }

    #[inline(always)]
    pub(crate) fn get_attributed_variable_list(&mut self) {
        let attr_var = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
        let attr_var_list = read_heap_cell!(attr_var,
            (HeapCellValueTag::AttrVar, h) => {
                h + 1
            }
            (HeapCellValueTag::Var | HeapCellValueTag::StackVar) => {
                // create an AttrVar in the heap.
                let h = self.machine_st.heap.len();

                self.machine_st.heap.push(attr_var_as_cell!(h));
                self.machine_st.heap.push(heap_loc_as_cell!(h+1));

                self.machine_st.bind(Ref::attr_var(h), attr_var);
                h + 1
            }
            _ => {
                self.machine_st.fail = true;
                return;
            }
        );

        let list_addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));
        self.machine_st.bind(Ref::heap_cell(attr_var_list), list_addr);
    }

    #[inline(always)]
    pub(crate) fn get_attr_var_queue_delimiter(&mut self) {
        let addr = self.machine_st.registers[1];
        let value = Fixnum::build_with(self.machine_st.attr_var_init.attr_var_queue.len() as i64);

        self.machine_st.unify_fixnum(value, self.machine_st.store(self.machine_st.deref(addr)));
    }

    #[inline(always)]
    pub(crate) fn get_attr_var_queue_beyond(&mut self) {
        let addr = self.machine_st.registers[1];
        let addr = self.machine_st.store(self.machine_st.deref(addr));

        let b = match Number::try_from(addr) {
            Ok(Number::Integer(n)) => n.to_usize(),
            Ok(Number::Fixnum(n)) => usize::try_from(n.get_num()).ok(),
            _ => {
                self.machine_st.fail = true;
                return;
            }
        };

        if let Some(b) = b {
            let iter = self.machine_st.gather_attr_vars_created_since(b);

            let var_list_addr = heap_loc_as_cell!(
                iter_to_heap_list(&mut self.machine_st.heap, iter)
            );

            let list_addr = self.machine_st.registers[2];
            unify!(self.machine_st, var_list_addr, list_addr);
        }
    }

    #[inline(always)]
    pub(crate) fn get_continuation_chunk(&mut self) {
        let e = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
        let e = cell_as_fixnum!(e).get_num() as usize;

        let p_functor = self.machine_st.store(self.machine_st.deref(
            self.machine_st.registers[2]
        ));

        let p = to_local_code_ptr(&self.machine_st.heap, p_functor).unwrap();

        let num_cells = *self.code[p].perm_vars_mut().unwrap();
        let mut addrs = vec![];

        for idx in 1..num_cells + 1 {
            addrs.push(self.machine_st.stack[stack_loc!(AndFrame, e, idx)]);
        }

        let chunk = str_loc_as_cell!(self.machine_st.heap.len());

        self.machine_st.heap.push(atom_as_cell!(atom!("cont_chunk"), 1 + num_cells));
        self.machine_st.heap.push(p_functor);
        self.machine_st.heap.extend(addrs);

        unify!(self.machine_st, self.machine_st.registers[3], chunk);
    }

    #[inline(always)]
    pub(crate) fn get_lifted_heap_from_offset_diff(&mut self) {
        let lh_offset = self.machine_st.registers[1];
        let lh_offset = cell_as_fixnum!(
            self.machine_st.store(self.machine_st.deref(lh_offset))
        ).get_num() as usize;

        if lh_offset >= self.machine_st.lifted_heap.len() {
            let solutions = self.machine_st.registers[2];
            let diff = self.machine_st.registers[3];

            unify_fn!(self.machine_st, solutions, diff);
        } else {
            let h = self.machine_st.heap.len();
            let mut last_index = h;

            for value in self.machine_st.lifted_heap[lh_offset ..].iter().cloned() {
                last_index = self.machine_st.heap.len();
                self.machine_st.heap.push(value + h);
            }

            if last_index < self.machine_st.heap.len() {
                let diff = self.machine_st.registers[3];
                unify_fn!(self.machine_st, diff, self.machine_st.heap[last_index]);
            }

            self.machine_st.lifted_heap.truncate(lh_offset);

            let solutions = self.machine_st.registers[2];
            unify_fn!(self.machine_st, heap_loc_as_cell!(h), solutions);
        }
    }

    #[inline(always)]
    pub(crate) fn get_lifted_heap_from_offset(&mut self) {
        let lh_offset = self.machine_st.registers[1];
        let lh_offset = cell_as_fixnum!(self.machine_st.store(self.machine_st.deref(
            lh_offset
        ))).get_num() as usize;

        if lh_offset >= self.machine_st.lifted_heap.len() {
            let solutions = self.machine_st.registers[2];
            unify_fn!(self.machine_st, solutions, empty_list_as_cell!());
        } else {
            let h = self.machine_st.heap.len();

            for addr in self.machine_st.lifted_heap[lh_offset..].iter().cloned() {
                self.machine_st.heap.push(addr + h);
            }

            self.machine_st.lifted_heap.truncate(lh_offset);

            let solutions = self.machine_st.registers[2];
            unify_fn!(self.machine_st, heap_loc_as_cell!(h), solutions);
        }
    }

    #[inline(always)]
    pub(crate) fn get_double_quotes(&mut self) {
        let a1 = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));

        self.machine_st.unify_atom(
            match self.machine_st.flags.double_quotes {
                DoubleQuotes::Chars => atom!("chars"),
                DoubleQuotes::Atom => atom!("atom"),
                DoubleQuotes::Codes => atom!("codes"),
            },
            a1,
        );
    }

    #[inline(always)]
    pub(crate) fn get_scc_cleaner(&mut self) {
        let dest = self.machine_st.registers[1];

        if let Some((addr, b_cutoff, prev_b)) = self.machine_st.cont_pts.pop() {
            let b = self.machine_st.stack.index_or_frame(self.machine_st.b).prelude.b;

            if b <= b_cutoff {
                self.machine_st.block = prev_b;

                if let Some(r) = dest.as_var() {
                    self.machine_st.bind(r, addr);
                    return;
                }
            } else {
                self.machine_st.cont_pts.push((addr, b_cutoff, prev_b));
            }
        }

        self.machine_st.fail = true;
    }

    #[inline(always)]
    pub(crate) fn halt(&mut self) {
        let code = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));

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

    #[inline(always)]
    pub(crate) fn install_scc_cleaner(&mut self) {
        let addr = self.machine_st.registers[1];
        let b = self.machine_st.b;
        let prev_block = self.machine_st.block;

        self.machine_st.run_cleaners_fn = Machine::run_cleaners;

        self.machine_st.install_new_block(self.machine_st.registers[2]);
        self.machine_st.cont_pts.push((addr, b, prev_block));
    }

    #[inline(always)]
    pub(crate) fn install_inference_counter(&mut self) -> CallResult {
        // A1 = B, A2 = L
        let a1 = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
        let a2 = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));

        let n = match Number::try_from(a2) {
            Ok(Number::Fixnum(bp)) => bp.get_num() as usize,
            Ok(Number::Integer(n)) => n.to_usize().unwrap(),
            _ => {
                let stub = functor_stub(
                    atom!("call_with_inference_limit"),
                    3,
                );

                let err = self.machine_st.type_error(ValidType::Integer, a2);
                return Err(self.machine_st.error_form(err, stub));
            }
        };

        let bp = cell_as_fixnum!(a1).get_num() as usize;
        let count = self.machine_st.cwil.add_limit(n, bp);
        let count = arena_alloc!(count.clone(), &mut self.machine_st.arena);

        self.machine_st.increment_call_count_fn = MachineState::increment_call_count;

        let a3 = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[3]));
        self.machine_st.unify_big_int(count, a3);

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn module_exists(&mut self) {
        let module = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
        let module_name = cell_as_atom!(module);

        self.machine_st.fail = !self.indices.modules.contains_key(&module_name);
    }

    pub(crate) fn predicate_defined(&self) -> bool {
        let module_name = cell_as_atom!(self.machine_st.store(self.machine_st.deref(
            self.machine_st.registers[1]
        )));

        let name = cell_as_atom!(self.machine_st.store(self.machine_st.deref(
            self.machine_st.registers[2]
        )));

        let arity = match Number::try_from(self.machine_st.store(self.machine_st.deref(
            self.machine_st.registers[3]
        ))) {
            Ok(Number::Fixnum(n))  => n.get_num() as usize,
            Ok(Number::Integer(n)) => {
                if let Some(n) = n.to_usize() {
                    n
                } else {
                    return false;
                }
            }
            _ => {
                unreachable!()
            }
        };

        self.indices.get_predicate_code_index(
            name,
            arity,
            module_name,
        ).map(|index| index.local().is_some())
         .unwrap_or(false)
    }

    #[inline(always)]
    pub(crate) fn no_such_predicate(&mut self) -> CallResult {
        let module_name = cell_as_atom!(self.machine_st.store(self.machine_st.deref(
            self.machine_st.registers[1]
        )));

        let head = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));

        self.machine_st.fail = read_heap_cell!(head,
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.machine_st.heap[s])
                    .get_name_and_arity();

                if ClauseType::is_inbuilt(name, arity) {
                    true
                } else {
                    let index = self.indices.get_predicate_code_index(
                        name,
                        arity,
                        module_name,
                    )
                        .map(|index| index.get())
                        .unwrap_or(IndexPtr::dynamic_undefined());

                    match index.tag() {
                        IndexPtrTag::DynamicUndefined | IndexPtrTag::Undefined => false,
                        _ => true,
                    }
                }
            }
            (HeapCellValueTag::Atom, (name, arity)) => {
                debug_assert_eq!(arity, 0);

                if ClauseType::is_inbuilt(name, 0) {
                    true
                } else {
                    let index = self.indices.get_predicate_code_index(
                        name,
                        0,
                        module_name,
                    )
                        .map(|index| index.get())
                        .unwrap_or(IndexPtr::dynamic_undefined());

                    match index.tag() {
                        IndexPtrTag::DynamicUndefined => false,
                        _ => true,
                    }
                }
            }
            _ => {
                let err = self.machine_st.type_error(ValidType::Callable, head);
                let stub = functor_stub(atom!("clause"), 2);

                return Err(self.machine_st.error_form(err, stub));
            }
        );

        Ok(())
    }
    #[inline(always)]
    pub(crate) fn redo_attr_var_binding(&mut self) {
        let var = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
        let value = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));

        debug_assert_eq!(HeapCellValueTag::AttrVar, var.get_tag());
        self.machine_st.heap[var.get_value()] = value;
    }

    #[inline(always)]
    pub(super) fn restore_instr_at_verify_attr_interrupt(&mut self) {
        match &self.code[VERIFY_ATTR_INTERRUPT_LOC] {
            &Instruction::VerifyAttrInterrupt => {}
            _ => {
                let instr = mem::replace(
                    &mut self.code[VERIFY_ATTR_INTERRUPT_LOC],
                    Instruction::VerifyAttrInterrupt,
                );

                self.code[self.machine_st.attr_var_init.cp] = instr;
            }
        }
    }

    #[inline(always)]
    pub(crate) fn reset_attr_var_state(&mut self) {
        self.restore_instr_at_verify_attr_interrupt();
        self.machine_st.attr_var_init.reset();
    }

    #[inline(always)]
    pub(crate) fn remove_call_policy_check(&mut self) {
        let bp = cell_as_fixnum!(self.machine_st.store(self.machine_st.deref(
            self.machine_st.registers[1]
        ))).get_num() as usize;

        if bp == self.machine_st.b && self.machine_st.cwil.is_empty() {
            self.machine_st.cwil.reset();
            self.machine_st.increment_call_count_fn = |_| { Ok(()) };
        }
    }

    #[inline(always)]
    pub(crate) fn remove_inference_counter(&mut self) {
        let a1 = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
        let bp = cell_as_fixnum!(a1).get_num() as usize;

        let count = self.machine_st.cwil.remove_limit(bp).clone();
        let count = arena_alloc!(count.clone(), &mut self.machine_st.arena);

        let a2 = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));

        self.machine_st.unify_big_int(count, a2);
    }

    #[inline(always)]
    pub(crate) fn return_from_verify_attr(&mut self) {
        let e = self.machine_st.e;
        let frame_len = self.machine_st.stack.index_and_frame(e).prelude.univ_prelude.num_cells;

        for i in 1..frame_len - 2 {
            self.machine_st.registers[i] = self.machine_st.stack[stack_loc!(AndFrame, e, i)];
        }

        self.machine_st.b0 = cell_as_fixnum!(self.machine_st.stack[stack_loc!(AndFrame, e, frame_len - 2)])
            .get_num() as usize;

        self.machine_st.num_of_args = cell_as_fixnum!(self.machine_st.stack[stack_loc!(AndFrame, e, frame_len - 1)])
            .get_num() as usize;

        let p = cell_as_fixnum!(self.machine_st.stack[stack_loc!(AndFrame, e, frame_len)]).get_num() as usize;

        self.machine_st.deallocate();
        self.machine_st.p = p;
    }

    #[inline(always)]
    pub(crate) fn restore_cut_policy(&mut self) {
        if self.machine_st.cont_pts.is_empty() {
            self.machine_st.run_cleaners_fn = |_| { false };
        }
    }

    #[inline(always)]
    pub(crate) fn set_cut_point(&mut self, r: RegType) -> bool {
        let cp = self.machine_st.store(self.machine_st.deref(self.machine_st[r]));
        self.machine_st.cut_body(cp);

        (self.machine_st.run_cleaners_fn)(self)
    }

    #[inline(always)]
    pub(crate) fn set_cut_point_by_default(&mut self, r: RegType) {
        let cp = self.machine_st.store(self.machine_st.deref(self.machine_st[r]));
        self.machine_st.cut_body(cp);
    }

    #[inline(always)]
    pub(crate) fn set_input(&mut self) -> CallResult {
        let addr = self.machine_st.store(self.machine_st.deref(
            self.machine_st.registers[1]
        ));

        let stream = self.machine_st.get_stream_or_alias(
            addr,
            &self.indices.stream_aliases,
            atom!("set_input"),
            1,
        )?;

        if !stream.is_input_stream() {
            let stub = functor_stub(atom!("set_input"), 1);
            let user_alias = atom_as_cell!(atom!("user"));

            let err = self.machine_st.permission_error(
                Permission::InputStream,
                atom!("stream"),
                user_alias,
            );

            return Err(self.machine_st.error_form(err, stub));
        }

        self.user_input = stream;
        Ok(())
    }

    #[inline(always)]
    pub(crate) fn set_output(&mut self) -> CallResult {
        let addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
        let stream = self.machine_st.get_stream_or_alias(
            addr,
            &self.indices.stream_aliases,
            atom!("set_output"),
            1,
        )?;

        if !stream.is_output_stream() {
            let stub = functor_stub(atom!("set_output"), 1);

            let user_alias = atom_as_cell!(atom!("user"));
            let err = self.machine_st.permission_error(
                Permission::OutputStream,
                atom!("stream"),
                user_alias,
            );

            return Err(self.machine_st.error_form(err, stub));
        }

        self.user_output = stream;
        Ok(())
    }

    #[inline(always)]
    pub(crate) fn set_double_quotes(&mut self) {
        let atom = cell_as_atom!(self.machine_st.registers[1]);

        self.machine_st.flags.double_quotes = match atom {
            atom!("atom") => DoubleQuotes::Atom,
            atom!("chars") => DoubleQuotes::Chars,
            atom!("codes") => DoubleQuotes::Codes,
            _ => {
                self.machine_st.fail = true;
                return;
            }
        };
    }

    #[inline(always)]
    pub(crate) fn inference_level(&mut self) {
        let a1 = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
        let a2 = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));

        let bp = cell_as_fixnum!(a2).get_num() as usize;
        let prev_b = self.machine_st.stack.index_or_frame(self.machine_st.b).prelude.b;

        if prev_b <= bp {
            self.machine_st.unify_atom(atom!("!"), a1)
        } else {
            self.machine_st.unify_atom(atom!("true"), a1);
        }
    }

    #[inline(always)]
    pub(crate) fn clean_up_block(&mut self) {
        let nb = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
        let nb = cell_as_fixnum!(nb).get_num() as usize;

        let b = self.machine_st.b;

        if nb > 0 && self.machine_st.stack.index_or_frame(b).prelude.b == nb {
            self.machine_st.b = self.machine_st.stack.index_or_frame(nb).prelude.b;
        }
    }

    #[inline(always)]
    pub(crate) fn get_ball(&mut self) {
        let addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
        let h = self.machine_st.heap.len();

        if self.machine_st.ball.stub.len() > 0 {
            let stub = self.machine_st.ball.copy_and_align(h);
            self.machine_st.heap.extend(stub.into_iter());
        } else {
            self.machine_st.fail = true;
            return;
        }

        match addr.as_var() {
            Some(r) => self.machine_st.bind(r, self.machine_st.heap[h]),
            _ => self.machine_st.fail = true,
        };
    }

    #[inline(always)]
    pub(crate) fn push_ball_stack(&mut self) {
        if self.machine_st.ball.stub.len() > 0 {
            self.machine_st.ball_stack.push(
                mem::replace(&mut self.machine_st.ball, Ball::new())
            );
        } else {
            self.machine_st.fail = true;
        }
    }

    #[inline(always)]
    pub(crate) fn pop_ball_stack(&mut self) {
        self.machine_st.ball_stack.pop();
    }

    #[inline(always)]
    pub(crate) fn pop_from_ball_stack(&mut self) {
        if let Some(ball) = self.machine_st.ball_stack.pop() {
            self.machine_st.ball = ball;
        }
    }

    #[inline(always)]
    pub(crate) fn get_current_block(&mut self) {
        let n = Fixnum::build_with(i64::try_from(self.machine_st.block).unwrap());
        self.machine_st.unify_fixnum(n, self.machine_st.registers[1]);
    }

    #[inline(always)]
    pub(crate) fn get_b_value(&mut self) {
        let n = Fixnum::build_with(i64::try_from(self.machine_st.b).unwrap());
        self.machine_st.unify_fixnum(n, self.machine_st.registers[1]);
    }

    #[inline(always)]
    pub(crate) fn get_cut_point(&mut self) {
        let n = Fixnum::build_with(i64::try_from(self.machine_st.b0).unwrap());
        self.machine_st.unify_fixnum(n, self.machine_st.registers[1]);
    }

    #[inline(always)]
    pub(crate) fn get_staggered_cut_point(&mut self) {
        use std::sync::Once;

        let b = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));

        static mut SEMICOLON_SECOND_BRANCH_LOC: usize = 0;
        static LOC_INIT: Once = Once::new();

        let semicolon_second_clause_p = unsafe {
            LOC_INIT.call_once(|| {
                if let Some(builtins) = self.indices.modules.get(&atom!("builtins")) {
                    match builtins.code_dir.get(&(atom!("staggered_sc"), 2)).map(|cell| cell.get()) {
                        Some(ip) if ip.tag() == IndexPtrTag::Index => {
                            let p = ip.p() as usize;

                            match &self.code[p] {
                                &Instruction::TryMeElse(o) => {
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
                } else {
                    unreachable!();
                }
            });

            SEMICOLON_SECOND_BRANCH_LOC
        };

        let staggered_b0 = if self.machine_st.b > 0 {
            let or_frame = self.machine_st.stack.index_or_frame(self.machine_st.b);

            if or_frame.prelude.bp == semicolon_second_clause_p {
                or_frame.prelude.b0
            } else {
                self.machine_st.b0
            }
        } else {
            self.machine_st.b0
        };

        let staggered_b0 = integer_as_cell!(
            Number::arena_from(staggered_b0, &mut self.machine_st.arena)
        );

        self.machine_st.bind(b.as_var().unwrap(), staggered_b0);
    }

    #[inline(always)]
    pub(crate) fn next_ep(&mut self) {
        let first_arg = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));

        let next_ep_atom = |machine_st: &mut MachineState, name, arity| {
            debug_assert_eq!(name, atom!("first"));
            debug_assert_eq!(arity, 0);

            if machine_st.e == 0 {
                machine_st.fail = true;
                return;
            }

            let and_frame = machine_st.stack.index_and_frame(machine_st.e);
            let cp = and_frame.prelude.cp - 1;

            let e = and_frame.prelude.e;
            let e = Fixnum::build_with(i64::try_from(e).unwrap());

            let p = str_loc_as_cell!(machine_st.heap.len());

            machine_st.heap.extend(functor!(atom!("dir_entry"), [fixnum(cp)]));
            machine_st.unify_fixnum(e, machine_st.registers[2]);

            if !machine_st.fail {
                unify!(machine_st, p, machine_st.registers[3]);
            }
        };

        read_heap_cell!(first_arg,
            (HeapCellValueTag::Atom, (name, arity)) => {
                next_ep_atom(&mut self.machine_st, name, arity);
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.machine_st.heap[s])
                    .get_name_and_arity();

                next_ep_atom(&mut self.machine_st, name, arity);
            }
            (HeapCellValueTag::Fixnum, n) => {
                let e = n.get_num() as usize;

                if e == 0 {
                    self.machine_st.fail = true;
                    return;
                }

                // get the call site so that the number of
                // active permanent variables can be read from
                // it later.
                let and_frame = self.machine_st.stack.index_and_frame(e);
                let cp = and_frame.prelude.cp - 1;

                let p = str_loc_as_cell!(self.machine_st.heap.len());
                self.machine_st.heap.extend(functor!(atom!("dir_entry"), [fixnum(cp)]));

                let e = Fixnum::build_with(i64::try_from(and_frame.prelude.e).unwrap());
                self.machine_st.unify_fixnum(e, self.machine_st.registers[2]);

                if !self.machine_st.fail {
                    unify!(self.machine_st, p, self.machine_st.registers[3]);
                }
            }
            _ => {
                unreachable!();
            }
        );
    }

    #[inline(always)]
    pub(crate) fn points_to_continuation_reset_marker(&mut self) {
        let addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));

        let p = match to_local_code_ptr(&self.machine_st.heap, addr) {
            Some(p) => p + 1,
            None => {
                self.machine_st.fail = true;
                return;
            }
        };

        if !self.is_reset_cont_marker(p) {
            self.machine_st.fail = true;
        }
    }

    #[inline(always)]
    pub(crate) fn quoted_token(&mut self) {
        let addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));

        read_heap_cell!(addr,
            (HeapCellValueTag::Fixnum, n) => {
                let n = u32::try_from(n.get_num()).ok();
                let n = n.and_then(std::char::from_u32);

                self.machine_st.fail = match n {
                    Some(c) => non_quoted_token(once(c)),
                    None => true,
                };
            }
            (HeapCellValueTag::Char, c) => {
                self.machine_st.fail = non_quoted_token(once(c));
            }
            (HeapCellValueTag::Atom, (name, arity)) => {
                debug_assert_eq!(arity, 0);
                self.machine_st.fail = non_quoted_token(name.as_str().chars());
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.machine_st.heap[s])
                    .get_name_and_arity();

                debug_assert_eq!(arity, 0);
                self.machine_st.fail = non_quoted_token(name.as_str().chars());
            }
            _ => {
                self.machine_st.fail = true;
            }
        );
    }

    #[inline(always)]
    pub(crate) fn read_query_term(&mut self) -> CallResult {
        self.user_input.reset();

        set_prompt(true);
        // let result = self.machine_st.read_term(self.user_input, &mut self.indices);
        let result = self.machine_st.read_term_from_user_input(self.user_input, &mut self.indices);
        set_prompt(false);

        match result {
            Ok(()) => Ok(()),
            Err(e) => {
                self.user_input.reset();
                return Err(e);
            }
        }
    }

    #[inline(always)]
    pub(crate) fn read_term(&mut self) -> CallResult {
        set_prompt(false);

        let stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices.stream_aliases,
            atom!("read_term"),
            3,
        )?;

        self.machine_st.read_term(stream, &mut self.indices)
    }

    #[inline(always)]
    pub(crate) fn read_term_from_chars(&mut self) -> CallResult {
        if let Some(atom_or_string) = self.machine_st.value_to_str_like(self.machine_st.registers[1]) {
            let chars = atom_or_string.to_string();
            let stream = Stream::from_owned_string(chars, &mut self.machine_st.arena);

            let term_write_result = match self.machine_st.read(stream, &self.indices.op_dir) {
                Ok(term_write_result) => term_write_result,
                Err(e) => {
                    let stub = functor_stub(atom!("read_term_from_chars"), 2);
                    let e = self.machine_st.session_error(SessionError::from(e));

                    return Err(self.machine_st.error_form(e, stub));
                }
            };

            let result = heap_loc_as_cell!(term_write_result.heap_loc);
            let var = self.machine_st.store(self.machine_st.deref(
                self.machine_st.registers[2]
            )).as_var().unwrap();

            self.machine_st.bind(var, result);
        } else {
            unreachable!()
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn reset_block(&mut self) {
        let addr = self.machine_st.deref(self.machine_st.registers[1]);
        self.machine_st.reset_block(addr);
    }

    #[inline(always)]
    pub(crate) fn reset_continuation_marker(&mut self) {
        let h = self.machine_st.heap.len();

        self.machine_st.registers[3] = atom_as_cell!(atom!("none"));
        self.machine_st.registers[4] = heap_loc_as_cell!(h);

        self.machine_st.heap.push(heap_loc_as_cell!(h));
    }

    #[inline(always)]
    pub(crate) fn set_ball(&mut self) {
        self.machine_st.set_ball();
    }

    #[inline(always)]
    pub(crate) fn set_seed(&mut self) {
        let seed = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
        let mut rand = RANDOM_STATE.borrow_mut();

        match Number::try_from(seed) {
            Ok(Number::Fixnum(n)) => rand.seed(&Integer::from(n)),
            Ok(Number::Integer(n)) => rand.seed(&*n),
            Ok(Number::Rational(n)) if n.denom() == &1 => rand.seed(n.numer()),
            _ => {
                self.machine_st.fail = true;
            }
        }
    }

    #[inline(always)]
    pub(crate) fn sleep(&mut self) {
        let time = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));

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

    #[inline(always)]
    pub(crate) fn socket_client_open(&mut self) -> CallResult {
        let addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
        let port = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));

        let socket_atom = cell_as_atom!(addr);

        let port = read_heap_cell!(port,
            (HeapCellValueTag::Atom, (name, arity)) => {
                debug_assert_eq!(arity, 0);
                name
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.machine_st.heap[s])
                    .get_name_and_arity();

                debug_assert_eq!(arity, 0);
                name
            }
            _ => {
                self.machine_st.atom_tbl.build_with(&match Number::try_from(port) {
                    Ok(Number::Fixnum(n)) => n.get_num().to_string(),
                    Ok(Number::Integer(n)) => n.to_string(),
                    _ => {
                        unreachable!()
                    }
                })
            }
        );

        let socket_addr = if socket_atom == atom!("") {
            atom!("127.0.0.1:80")
        } else {
            let buffer = format!("{}:{}", socket_atom.as_str(), port.as_str());
            self.machine_st.atom_tbl.build_with(&buffer)
        };

        let alias = self.machine_st.registers[4];
        let eof_action = self.machine_st.registers[5];
        let reposition = self.machine_st.registers[6];
        let stream_type = self.machine_st.registers[7];

        let options = self.machine_st.to_stream_options(alias, eof_action, reposition, stream_type);

        if options.reposition() {
            return Err(self.machine_st.reposition_error(atom!("socket_client_open"), 3));
        }

        if let Some(alias) = options.get_alias() {
            if self.indices.stream_aliases.contains_key(&alias) {
                return Err(self.machine_st.occupied_alias_permission_error(
                    alias,
                    atom!("socket_client_open"),
                    3,
                ));
            }
        }

        let stream = match TcpStream::connect(socket_addr.as_str()).map_err(|e| e.kind()) {
            Ok(tcp_stream) => {
                let mut stream = Stream::from_tcp_stream(socket_addr, tcp_stream, &mut self.machine_st.arena);

                *stream.options_mut() = options;

                if let Some(alias) = stream.options().get_alias() {
                    self.indices.stream_aliases.insert(alias, stream);
                }

                self.indices.streams.insert(stream);

                stream_as_cell!(stream)
            }
            Err(ErrorKind::PermissionDenied) => {
                return Err(self.machine_st.open_permission_error(addr, atom!("socket_client_open"), 3));
            }
            Err(ErrorKind::NotFound) => {
                let stub = functor_stub(atom!("socket_client_open"), 3);
                let err = self.machine_st.existence_error(
                    ExistenceError::SourceSink(addr),
                );

                return Err(self.machine_st.error_form(err, stub));
            }
            Err(_) => {
                // for now, just fail. expand to meaningful error messages later.
                self.machine_st.fail = true;
                return Ok(());
            }
        };

        let stream_addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[3]));
        self.machine_st.bind(stream_addr.as_var().unwrap(), stream);

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn socket_server_open(&mut self) -> CallResult {
        let addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
        let socket_atom = cell_as_atom_cell!(addr).get_name();

        let socket_atom = if socket_atom == atom!("[]") {
            atom!("127.0.0.1")
        } else {
            socket_atom
        };

        let port = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));

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
                        (arena_alloc!(tcp_listener, &mut self.machine_st.arena), port as usize)
                    } else {
                        self.machine_st.fail = true;
                        return Ok(());
                    }
                }
                Err(ErrorKind::PermissionDenied) => {
                    return Err(self.machine_st.open_permission_error(addr, atom!("socket_server_open"), 2));
                }
                _ => {
                    self.machine_st.fail = true;
                    return Ok(());
                }
            };

        let addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[3]));
        self.machine_st.bind(addr.as_var().unwrap(), typed_arena_ptr_as_cell!(tcp_listener));

        if had_zero_port {
            self.machine_st.unify_fixnum(Fixnum::build_with(port as i64), self.machine_st.registers[2]);
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn socket_server_accept(&mut self) -> CallResult {
        let alias = self.machine_st.registers[4];
        let eof_action = self.machine_st.registers[5];
        let reposition = self.machine_st.registers[6];
        let stream_type = self.machine_st.registers[7];

        let options = self.machine_st.to_stream_options(alias, eof_action, reposition, stream_type);

        if options.reposition() {
            return Err(self.machine_st.reposition_error(atom!("socket_server_accept"), 4));
        }

        if let Some(alias) = options.get_alias() {
            if self.indices.stream_aliases.contains_key(&alias) {
                return Err(self.machine_st.occupied_alias_permission_error(
                    alias,
                    atom!("socket_server_accept"),
                    4,
                ));
            }
        }

        let culprit = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));

        read_heap_cell!(culprit,
            (HeapCellValueTag::Cons, cons_ptr) => {
                match_untyped_arena_ptr!(cons_ptr,
                     (ArenaHeaderTag::TcpListener, tcp_listener) => {
                         match tcp_listener.accept().ok() {
                             Some((tcp_stream, socket_addr)) => {
                                 let client = self.machine_st.atom_tbl.build_with(&socket_addr.to_string());

                                 let mut tcp_stream = Stream::from_tcp_stream(
                                     client,
                                     tcp_stream,
                                     &mut self.machine_st.arena,
                                 );

                                 *tcp_stream.options_mut() = options;

                                 if let Some(alias) = &tcp_stream.options().get_alias() {
                                     self.indices.stream_aliases.insert(*alias, tcp_stream);
                                 }

                                 self.indices.streams.insert(tcp_stream);

                                 let tcp_stream = stream_as_cell!(tcp_stream);
                                 let client = atom_as_cell!(client);

                                 let client_addr = self.machine_st.store(self.machine_st.deref(
                                     self.machine_st.registers[2],
                                 ));
                                 let stream_addr = self.machine_st.store(self.machine_st.deref(
                                     self.machine_st.registers[3],
                                 ));

                                 self.machine_st.bind(client_addr.as_var().unwrap(), client);
                                 self.machine_st.bind(stream_addr.as_var().unwrap(), tcp_stream);
                             }
                             None => {
                                 self.machine_st.fail = true;
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

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn tls_client_connect(&mut self) -> CallResult {
        if let Some(hostname) = self.machine_st.value_to_str_like(self.machine_st.registers[1]) {
            let stream0 = self.machine_st.get_stream_or_alias(
                self.machine_st.registers[2],
                &self.indices.stream_aliases,
                atom!("tls_client_negotiate"),
                3,
            )?;

            let connector = TlsConnector::new().unwrap();
            let stream =
                match connector.connect(hostname.as_str(), stream0) {
                    Ok(tls_stream) => tls_stream,
                    Err(_) => {
                        return Err(self.machine_st.open_permission_error(
                            self.machine_st.registers[1],
                            atom!("tls_client_negotiate"),
                            3,
                        ));
                    }
                };

            let addr = atom!("TLS");
            let stream = Stream::from_tls_stream(addr, stream, &mut self.machine_st.arena);
            self.indices.streams.insert(stream);

            self.machine_st.heap.push(stream_as_cell!(stream));
            let stream_addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[3]));
            self.machine_st.bind(stream_addr.as_var().unwrap(), stream_as_cell!(stream));

            Ok(())
        } else {
            unreachable!();
        }
    }

    #[inline(always)]
    pub(crate) fn tls_accept_client(&mut self) -> CallResult {
        let pkcs12 = self.string_encoding_bytes(self.machine_st.registers[1], atom!("octet"));

        if let Some(password) = self.machine_st.value_to_str_like(self.machine_st.registers[2]) {
            let identity =
                match Identity::from_pkcs12(&pkcs12, password.as_str()) {
                    Ok(identity) => identity,
                    Err(_) => {
                        return Err(self.machine_st.open_permission_error(
                            self.machine_st.registers[1],
                            atom!("tls_server_negotiate"),
                            3,
                        ));
                    }
                };

            let stream0 = self.machine_st.get_stream_or_alias(
                self.machine_st.registers[3],
                &self.indices.stream_aliases,
                atom!("tls_server_negotiate"),
                3,
            )?;

            let acceptor = TlsAcceptor::new(identity).unwrap();

            let stream =
                match acceptor.accept(stream0) {
                    Ok(tls_stream) => tls_stream,
                    Err(_) => {
                        return Err(self.machine_st.open_permission_error(
                            self.machine_st.registers[3],
                            atom!("tls_server_negotiate"),
                            3,
                        ));
                    }
                };

            let stream = Stream::from_tls_stream(atom!("TLS"), stream, &mut self.machine_st.arena);
            self.indices.streams.insert(stream);

            let stream_addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[4]));
            self.machine_st.bind(stream_addr.as_var().unwrap(), stream_as_cell!(stream));
        } else {
            unreachable!();
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn socket_server_close(&mut self) -> CallResult {
        let culprit = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));

        read_heap_cell!(culprit,
            (HeapCellValueTag::Cons, cons_ptr) => {
                match_untyped_arena_ptr!(cons_ptr,
                    (ArenaHeaderTag::TcpListener, tcp_listener) => {
                        unsafe {
                            // dropping closes the instance.
                            std::ptr::drop_in_place(&mut tcp_listener as *mut _);
                        }

                        tcp_listener.set_tag(ArenaHeaderTag::Dropped);
                        return Ok(());
                    }
                    _ => {
                    }
                );
            }
            _ => {
            }
        );

        let err = self.machine_st.type_error(ValidType::TcpListener, culprit);
        let stub = functor_stub(atom!("socket_server_close"), 1);

        return Err(self.machine_st.error_form(err, stub));
    }

    #[inline(always)]
    pub(crate) fn set_stream_position(&mut self) -> CallResult {
        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices.stream_aliases,
            atom!("set_stream_position"),
            2,
        )?;

        if !stream.options().reposition() {
            let stub = functor_stub(atom!("set_stream_position"), 2);

            let err = self.machine_st.permission_error(
                Permission::Reposition,
                atom!("stream"),
                stream_as_cell!(stream),
            );

            return Err(self.machine_st.error_form(err, stub));
        }

        let position = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));

        let position = match Number::try_from(position) {
            Ok(Number::Fixnum(n)) => n.get_num() as u64,
            Ok(Number::Integer(n)) => {
                if let Some(n) = n.to_u64() {
                    n
                } else {
                    self.machine_st.fail = true;
                    return Ok(());
                }
            }
            _ => {
                unreachable!()
            }
        };

        stream.set_position(position);
        Ok(())
    }

    #[inline(always)]
    pub(crate) fn stream_property(&mut self) -> CallResult {
        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices.stream_aliases,
            atom!("stream_property"),
            2,
        )?;

        let atom = cell_as_atom!(self.machine_st.store(self.machine_st.deref(
            self.machine_st.registers[2]
        )));

        let property = match atom {
            atom!("file_name") => {
                atom_as_cell!(if let Some(file_name) = stream.file_name() {
                    file_name
                } else {
                    self.machine_st.fail = true;
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
                    self.machine_st.fail = true;
                    return Ok(());
                })
            }
            atom!("position") => {
                if let Some((position, lines_read)) = stream.position() {
                    let h = self.machine_st.heap.len();

                    let position_term = functor!(
                        atom!("position_and_lines_read"),
                        [integer(position, &mut self.machine_st.arena),
                         integer(lines_read, &mut self.machine_st.arena)]
                    );

                    self.machine_st.heap.extend(position_term.into_iter());
                    str_loc_as_cell!(h)
                } else {
                    self.machine_st.fail = true;
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

        unify!(self.machine_st, property, self.machine_st.registers[3]);
        Ok(())
    }

    #[inline(always)]
    pub(crate) fn store_global_var(&mut self) {
        let key = cell_as_atom!(self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1])));

        let value = self.machine_st.registers[2];
        let mut ball = Ball::new();

        ball.boundary = self.machine_st.heap.len();

        copy_term(
            CopyBallTerm::new(&mut self.machine_st.stack, &mut self.machine_st.heap, &mut ball.stub),
            value,
            AttrVarPolicy::DeepCopy,
        );

        self.indices.global_variables.insert(key, (ball, None));
    }

    #[inline(always)]
    pub(crate) fn store_backtrackable_global_var(&mut self) {
        let key = cell_as_atom!(self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1])));
        let new_value = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]));

        match self.indices.global_variables.get_mut(&key) {
            Some((_, ref mut loc)) => match loc {
                Some(ref mut value) => {
                    self.machine_st.trail(TrailRef::BlackboardOffset(key, *value));
                    *value = new_value;
                }
                loc @ None => {
                    self.machine_st.trail(TrailRef::BlackboardEntry(key));
                    *loc = Some(new_value);
                }
            },
            None => {
                self.machine_st.trail(TrailRef::BlackboardEntry(key));
                self.indices
                    .global_variables
                    .insert(key, (Ball::new(), Some(new_value)));
            }
        }
    }

    #[inline(always)]
    pub(crate) fn term_attributed_variables(&mut self) {
        if self.machine_st.registers[1].is_constant() {
            self.machine_st.unify_atom(
                atom!("[]"),
                self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2])),
            );

            return;
        }

        let seen_vars = self.machine_st.attr_vars_of_term(self.machine_st.registers[1]);
        let outcome = heap_loc_as_cell!(
            iter_to_heap_list(&mut self.machine_st.heap, seen_vars.into_iter())
        );

        unify_fn!(self.machine_st, self.machine_st.registers[2], outcome);
    }

    #[inline(always)]
    pub(crate) fn term_variables(&mut self) {
        let a1 = self.machine_st.registers[1];
        let a2 = self.machine_st.registers[2];

        let stored_v = self.machine_st.store(self.machine_st.deref(a1));

        if stored_v.is_constant() {
            self.machine_st.unify_atom(atom!("[]"), self.machine_st.store(self.machine_st.deref(a2)));
            return;
        }

        let mut seen_set = IndexSet::with_hasher(FxBuildHasher::default());

        self.machine_st.variable_set(&mut seen_set, stored_v);

        let outcome = heap_loc_as_cell!(
            iter_to_heap_list(&mut self.machine_st.heap, seen_set.into_iter())
        );

        unify_fn!(self.machine_st, a2, outcome);
    }

    #[inline(always)]
    pub(crate) fn term_variables_under_max_depth(&mut self) {
        // Term, MaxDepth, VarList
        let max_depth = cell_as_fixnum!(
            self.machine_st.store(self.machine_st.deref(self.machine_st.registers[2]))
        ).get_num() as usize;

        self.machine_st.term_variables_under_max_depth(
            self.machine_st.registers[1],
            max_depth,
            self.machine_st.registers[3],
        );
    }

    #[inline(always)]
    pub(crate) fn truncate_lifted_heap_to(&mut self) {
        let a1 = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
        let lh_offset = cell_as_fixnum!(a1).get_num() as usize;

        self.machine_st.lifted_heap.truncate(lh_offset);
    }

    #[inline(always)]
    pub(crate) fn unify_with_occurs_check(&mut self) {
        let a1 = self.machine_st.registers[1];
        let a2 = self.machine_st.registers[2];

        unify_with_occurs_check!(&mut self.machine_st, a1, a2);
    }

    #[inline(always)]
    pub(crate) fn unwind_environments(&mut self) -> bool {
        let mut e = self.machine_st.e;
        let mut cp = self.machine_st.cp;

        while e > 0 {
            if self.is_reset_cont_marker(cp) {
                self.machine_st.e = e;
                self.machine_st.p = cp + 1; // skip the reset marker.

                return true;
            }

            let and_frame = self.machine_st.stack.index_and_frame(e);

            cp = and_frame.prelude.cp;
            e = and_frame.prelude.e;
        }

        false
    }

    #[inline(always)]
    pub(crate) fn wam_instructions(&mut self) -> CallResult {
        let module_name = cell_as_atom!(self.machine_st.store(self.machine_st.deref(
            self.machine_st.registers[1])
        ));

        let name = self.machine_st.registers[2];
        let arity = self.machine_st.registers[3];

        let name = cell_as_atom!(self.machine_st.store(self.machine_st.deref(name)));
        let arity = self.machine_st.store(self.machine_st.deref(arity));

        let arity = match Number::try_from(arity) {
            Ok(Number::Fixnum(n)) => n.get_num() as usize,
            Ok(Number::Integer(n)) => n.to_usize().unwrap(),
            _ => {
                unreachable!()
            }
        };

        let key = (name, arity);

        let first_idx = match module_name {
            atom!("user") => self.indices.code_dir.get(&key),
            _ => match self.indices.modules.get(&module_name) {
                Some(module) => module.code_dir.get(&key),
                None => {
                    let stub = functor_stub(key.0, key.1);
                    let err = self.machine_st.session_error(
                        SessionError::from(CompilationError::InvalidModuleResolution(
                            module_name,
                        )),
                    );

                    return Err(self.machine_st.error_form(err, stub));
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
                let err = self.machine_st.existence_error(
                    ExistenceError::Procedure(name, arity),
                );

                return Err(self.machine_st.error_form(err, stub));
            }
        };

        let mut h = self.machine_st.heap.len();

        let mut functors = vec![];
        let mut functor_list = vec![];

        walk_code(&self.code, first_idx, |instr| {
            let old_len = functors.len();
            instr.enqueue_functors(h, &mut self.machine_st.arena, &mut functors);
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
            self.machine_st.heap.extend(functor.into_iter());
        }

        let listing = heap_loc_as_cell!(
            iter_to_heap_list(&mut self.machine_st.heap, functor_list.into_iter())
        );

        let listing_var = self.machine_st.registers[4];

        unify!(self.machine_st, listing, listing_var);
        Ok(())
    }

    #[inline(always)]
    pub(crate) fn write_term(&mut self) -> CallResult {
        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices.stream_aliases,
            atom!("write_term"),
            3,
        )?;

        self.machine_st.check_stream_properties(
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
            return Err(self.machine_st.stream_permission_error(
                Permission::OutputStream,
                err_atom,
                stream,
                atom!("write_term"),
                3,
            ));
        }

        let printer = match self.machine_st.write_term(&self.indices.op_dir)? {
            Some(printer) => printer,
            None => {
                // this next line is executed by
                // MachineState::write_term in this case. it's
                // commented here because rustc can't prove
                // that it's no longer borrowed.

                // self.machine_st.fail = true;
                return Ok(());
            }
        };

        let output = printer.print();

        match write!(&mut stream, "{}", output.result()) {
            Ok(_) => {}
            Err(_) => {
                let stub = functor_stub(atom!("open"), 4);
                let err = self.machine_st.existence_error(
                    ExistenceError::Stream(self.machine_st.registers[1]),
                );

                return Err(self.machine_st.error_form(err, stub));
            }
        }

        stream.flush().unwrap();
        Ok(())
    }

    #[inline(always)]
    pub(crate) fn write_term_to_chars(&mut self) -> CallResult {
        let printer = match self.machine_st.write_term(&self.indices.op_dir)? {
            None => {
                // this next line is executed by
                // MachineState::write_term in this case. it's
                // commented here because rustc can't prove
                // that it's no longer borrowed.

                // self.machine_st.fail = true;
                return Ok(());
            }
            Some(printer) => printer,
        };

        let result = printer.print().result();
        let chars = put_complete_string(
            &mut self.machine_st.heap,
            &result,
            &mut self.machine_st.atom_tbl,
        );

        let result_addr = self.machine_st.store(self.machine_st.deref(
            self.machine_st.registers[1]
        ));

        if let Some(var) = result_addr.as_var() {
            self.machine_st.bind(var, chars);
        } else {
            unreachable!()
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn scryer_prolog_version(&mut self) {
        use git_version::git_version;

        let buffer = git_version!(cargo_prefix = "cargo:", fallback = "unknown");
        let buffer_atom = self.machine_st.atom_tbl.build_with(buffer);

        self.machine_st.unify_complete_string(
            buffer_atom,
            self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1])),
        );
    }

    #[inline(always)]
    pub(crate) fn crypto_random_byte(&mut self) {
        let arg = self.machine_st.registers[1];
        let mut bytes: [u8; 1] = [0];

        match rng().fill(&mut bytes) {
            Ok(()) => {}
            Err(_) => {
                // the error payload here is of type 'Unspecified',
                // which contains no information whatsoever. So, for now,
                // just fail.
                self.machine_st.fail = true;
                return;
            }
        }

        let byte = Fixnum::build_with(bytes[0] as i64);
        self.machine_st.unify_fixnum(byte, arg);
    }

    #[inline(always)]
    pub(crate) fn crypto_data_hash(&mut self) {
        let encoding = cell_as_atom!(self.machine_st.registers[2]);
        let bytes = self.string_encoding_bytes(self.machine_st.registers[1], encoding);

        let algorithm = cell_as_atom!(self.machine_st.registers[4]);

        let ints_list = match algorithm {
            atom!("sha3_224") => {
                let mut context = Sha3_224::new();
                context.input(&bytes);

                heap_loc_as_cell!(
                    iter_to_heap_list(
                        &mut self.machine_st.heap,
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
                        &mut self.machine_st.heap,
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
                        &mut self.machine_st.heap,
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
                        &mut self.machine_st.heap,
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
                        &mut self.machine_st.heap,
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
                        &mut self.machine_st.heap,
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
                        &mut self.machine_st.heap,
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
                        &mut self.machine_st.heap,
                        ints.as_ref()
                            .iter()
                            .map(|b| fixnum_as_cell!(Fixnum::build_with(*b as i64))),
                    )
                )
            }
        };

        unify!(self.machine_st, self.machine_st.registers[3], ints_list);
    }

    #[inline(always)]
    pub(crate) fn crypto_data_hkdf(&mut self) {
        let encoding = cell_as_atom!(self.machine_st.registers[2]);
        let data = self.string_encoding_bytes(self.machine_st.registers[1], encoding);

        let stub1_gen = || functor_stub(atom!("crypto_data_hkdf"), 4);
        let salt = self.machine_st.integers_to_bytevec(self.machine_st.registers[3], stub1_gen);

        let stub2_gen = || functor_stub(atom!("crypto_data_hkdf"), 4);
        let info = self.machine_st.integers_to_bytevec(self.machine_st.registers[4], stub2_gen);

        let algorithm = cell_as_atom!(self.machine_st.registers[5]);

        let length = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[6]));

        let length = match Number::try_from(length) {
            Ok(Number::Fixnum(n)) => usize::try_from(n.get_num()).unwrap(),
            Ok(Number::Integer(n)) => match n.to_usize() {
                Some(u) => u,
                _ => {
                    self.machine_st.fail = true;
                    return;
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
                    self.machine_st.fail = true;
                    return;
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
                    self.machine_st.fail = true;
                    return;
                }
            }

            heap_loc_as_cell!(
                iter_to_heap_list(
                    &mut self.machine_st.heap,
                    bytes
                        .iter()
                        .map(|b| fixnum_as_cell!(Fixnum::build_with(*b as i64))),
                )
            )
        };

        unify!(self.machine_st, self.machine_st.registers[7], ints_list);
    }

    #[inline(always)]
    pub(crate) fn crypto_password_hash(&mut self) {
        let stub1_gen = || functor_stub(atom!("crypto_password_hash"), 3);
        let data = self.machine_st.integers_to_bytevec(self.machine_st.registers[1], stub1_gen);
        let stub2_gen = || functor_stub(atom!("crypto_password_hash"), 3);
        let salt = self.machine_st.integers_to_bytevec(self.machine_st.registers[2], stub2_gen);

        let iterations = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[3]));

        let iterations = match Number::try_from(iterations) {
            Ok(Number::Fixnum(n)) => u64::try_from(n.get_num()).unwrap(),
            Ok(Number::Integer(n)) => match n.to_u64() {
                Some(i) => i,
                None => {
                    self.machine_st.fail = true;
                    return;
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
                    &mut self.machine_st.heap,
                    bytes
                        .iter()
                        .map(|b| fixnum_as_cell!(Fixnum::build_with(*b as i64))),
                )
            )
        };

        unify!(self.machine_st, self.machine_st.registers[4], ints_list);
    }

    #[inline(always)]
    pub(crate) fn crypto_data_encrypt(&mut self) {
        let encoding = cell_as_atom!(self.machine_st.registers[3]);

        let data = self.string_encoding_bytes(self.machine_st.registers[1], encoding);
        let aad = self.string_encoding_bytes(self.machine_st.registers[2], encoding);

        let stub2_gen = || functor_stub(atom!("crypto_data_encrypt"), 7);
        let key = self.machine_st.integers_to_bytevec(self.machine_st.registers[4], stub2_gen);

        let stub3_gen = || functor_stub(atom!("crypto_data_encrypt"), 7);
        let iv = self.machine_st.integers_to_bytevec(self.machine_st.registers[5], stub3_gen);

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
                self.machine_st.fail = true;
                return;
            }
        };

        let tag_list = heap_loc_as_cell!(
            iter_to_heap_list(
                &mut self.machine_st.heap,
                tag.as_ref()
                    .iter()
                    .map(|b| fixnum_as_cell!(Fixnum::build_with(*b as i64))),
            )
        );

        let complete_string = self.u8s_to_string(&in_out);

        unify!(self.machine_st, self.machine_st.registers[6], tag_list);
        unify!(self.machine_st, self.machine_st.registers[7], complete_string);
    }

    #[inline(always)]
    pub(crate) fn crypto_data_decrypt(&mut self) {
        let data = self.string_encoding_bytes(self.machine_st.registers[1], atom!("octet"));
        let encoding = cell_as_atom!(self.machine_st.registers[5]);

        let aad = self.string_encoding_bytes(self.machine_st.registers[2], encoding);
        let stub1_gen = || functor_stub(atom!("crypto_data_decrypt"), 7);

        let key = self.machine_st.integers_to_bytevec(self.machine_st.registers[3], stub1_gen);
        let stub2_gen = || functor_stub(atom!("crypto_data_decrypt"), 7);
        let iv = self.machine_st.integers_to_bytevec(self.machine_st.registers[4], stub2_gen);

        let unbound_key = aead::UnboundKey::new(&aead::CHACHA20_POLY1305, &key).unwrap();
        let nonce = aead::Nonce::try_assume_unique_for_key(&iv).unwrap();
        let key = aead::LessSafeKey::new(unbound_key);

        let mut in_out = data;

        let complete_string = {
            let decrypted_data =
                match key.open_in_place(nonce, aead::Aad::from(aad), &mut in_out) {
                    Ok(d) => d,
                    _ => {
                        self.machine_st.fail = true;
                        return;
                    }
                };

            let buffer = match encoding {
                atom!("octet") => String::from_iter(decrypted_data.iter().map(|b| *b as char)),
                atom!("utf8") => match String::from_utf8(decrypted_data.to_vec()) {
                    Ok(str) => str,
                    _ => {
                        self.machine_st.fail = true;
                        return;
                    }
                },
                _ => {
                    unreachable!()
                }
            };

            if buffer.len() == 0 {
                empty_list_as_cell!()
            } else {
                atom_as_cstr_cell!(self.machine_st.atom_tbl.build_with(&buffer))
            }
        };

        unify!(self.machine_st, self.machine_st.registers[6], complete_string);
    }

    #[inline(always)]
    pub(crate) fn crypto_curve_scalar_mult(&mut self) {

        let stub_gen = || functor_stub(atom!("crypto_curve_scalar_mult"), 4);
        let scalar_bytes = self.machine_st.integers_to_bytevec(self.machine_st.registers[2], stub_gen);
        let point_bytes = self.machine_st.integers_to_bytevec(self.machine_st.registers[3], stub_gen);

        let mut point = secp256k1::Point::decode(&point_bytes).unwrap();
        let scalar = secp256k1::Scalar::decode_reduce(&scalar_bytes);
        point *= scalar;

        let uncompressed = self.u8s_to_string(&point.encode_uncompressed());

        unify!(self.machine_st, self.machine_st.registers[4], uncompressed);
    }

    #[inline(always)]
    pub(crate) fn ed25519_new_key_pair(&mut self) {
        let pkcs8_bytes = signature::Ed25519KeyPair::generate_pkcs8(rng()).unwrap();
        let complete_string = self.u8s_to_string(pkcs8_bytes.as_ref());

        unify!(self.machine_st, self.machine_st.registers[1], complete_string)
    }

    #[inline(always)]
    pub(crate) fn ed25519_key_pair_public_key(&mut self) {
        let bytes = self.string_encoding_bytes(self.machine_st.registers[1], atom!("octet"));

        let key_pair = match signature::Ed25519KeyPair::from_pkcs8(&bytes) {
            Ok(kp) => kp,
            _ => {
                self.machine_st.fail = true;
                return;
            }
        };

        let complete_string = self.u8s_to_string(key_pair.public_key().as_ref());

        unify!(self.machine_st, self.machine_st.registers[2], complete_string);
    }

    #[inline(always)]
    pub(crate) fn ed25519_sign(&mut self) {
        let key = self.string_encoding_bytes(self.machine_st.registers[1], atom!("octet"));
        let encoding = cell_as_atom!(self.machine_st.registers[3]);
        let data = self.string_encoding_bytes(self.machine_st.registers[2], encoding);

        let key_pair = match signature::Ed25519KeyPair::from_pkcs8(&key) {
            Ok(kp) => kp,
            _ => {
                self.machine_st.fail = true;
                return;
            }
        };

        let sig = key_pair.sign(&data);

        let sig_list = heap_loc_as_cell!(
            iter_to_heap_list(
                &mut self.machine_st.heap,
                sig.as_ref()
                    .iter()
                    .map(|b| fixnum_as_cell!(Fixnum::build_with(*b as i64))),
            )
        );

        unify!(self.machine_st, self.machine_st.registers[4], sig_list);
    }

    #[inline(always)]
    pub(crate) fn ed25519_verify(&mut self) {
        let key = self.string_encoding_bytes(self.machine_st.registers[1], atom!("octet"));
        let encoding = cell_as_atom!(self.machine_st.registers[3]);
        let data = self.string_encoding_bytes(self.machine_st.registers[2], encoding);
        let stub_gen = || functor_stub(atom!("ed25519_verify"), 5);
        let signature = self.machine_st.integers_to_bytevec(self.machine_st.registers[4], stub_gen);

        let peer_public_key = signature::UnparsedPublicKey::new(&signature::ED25519, &key);

        match peer_public_key.verify(&data, &signature) {
            Ok(_) => {}
            _ => {
                self.machine_st.fail = true;
            }
        }
    }

    #[inline(always)]
    pub(crate) fn curve25519_scalar_mult(&mut self) {
        let stub1_gen = || functor_stub(atom!("curve25519_scalar_mult"), 3);
        let scalar_bytes = self.machine_st.integers_to_bytevec(self.machine_st.registers[1], stub1_gen);
        let scalar = Scalar(<[u8; 32]>::try_from(&scalar_bytes[..]).unwrap());

        let stub2_gen = || functor_stub(atom!("curve25519_scalar_mult"), 3);
        let point_bytes = self.machine_st.integers_to_bytevec(self.machine_st.registers[2], stub2_gen);
        let point = GroupElement(<[u8; 32]>::try_from(&point_bytes[..]).unwrap());

        let result = scalarmult(&scalar, &point).unwrap();

        let string = self.u8s_to_string(&result[..]);

        unify!(self.machine_st, self.machine_st.registers[3], string);
    }

    #[inline(always)]
    pub(crate) fn first_non_octet(&mut self) {
        let addr = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));

        if let Some(string) = self.machine_st.value_to_str_like(addr) {
            for c in string.as_str().chars() {
                if c as u32 > 255 {
                    let non_octet = self.machine_st.atom_tbl.build_with(&c.to_string());
                    self.machine_st.unify_atom(non_octet, self.machine_st.registers[2]);
                    return;
                }
            }
        }

        self.machine_st.fail = true;
    }

    #[inline(always)]
    pub(crate) fn load_html(&mut self) {
        if let Some(string) = self.machine_st.value_to_str_like(self.machine_st.registers[1]) {
            let doc = select::document::Document::from_read(string.as_str().as_bytes()).unwrap();
            let result = self.html_node_to_term(doc.nth(0).unwrap());

            unify!(self.machine_st, self.machine_st.registers[2], result);
        } else {
            self.machine_st.fail = true;
        }
    }

    #[inline(always)]
    pub(crate) fn load_xml(&mut self) {
        if let Some(string) = self.machine_st.value_to_str_like(self.machine_st.registers[1]) {
            match roxmltree::Document::parse(string.as_str()) {
                Ok(doc) => {
                    let result = self.xml_node_to_term(doc.root_element());
                    unify!(self.machine_st, self.machine_st.registers[2], result);
                }
                _ => {
                    self.machine_st.fail = true;
                }
            }
        } else {
            self.machine_st.fail = true;
        }
    }

    #[inline(always)]
    pub(crate) fn get_env(&mut self) {
        if let Some(key) = self.machine_st.value_to_str_like(self.machine_st.registers[1]) {
            match env::var(key.as_str()) {
                Ok(value) => {
                    let cstr = put_complete_string(
                        &mut self.machine_st.heap,
                        &value,
                        &mut self.machine_st.atom_tbl,
                    );

                    unify!(self.machine_st, self.machine_st.registers[2], cstr);
                }
                _ => {
                    self.machine_st.fail = true;
                }
            }
        } else {
            self.machine_st.fail = true;
        }
    }

    #[inline(always)]
    pub(crate) fn set_env(&mut self) {
        let key = self.machine_st.value_to_str_like(self.machine_st.registers[1]).unwrap();
        let value = self.machine_st.value_to_str_like(self.machine_st.registers[2]).unwrap();

        env::set_var(key.as_str(), value.as_str());
    }

    #[inline(always)]
    pub(crate) fn unset_env(&mut self) {
        let key = self.machine_st.value_to_str_like(self.machine_st.registers[1]).unwrap();
        env::remove_var(key.as_str());
    }

    #[inline(always)]
    pub(crate) fn pid(&mut self) {
        let pid = process::id();

        match fixnum!(Number, pid as i64, &mut self.machine_st.arena) {
            Number::Fixnum(pid) => {
                self.machine_st.unify_fixnum(pid, self.machine_st.registers[1]);
            }
            Number::Integer(pid) => {
                self.machine_st.unify_big_int(pid, self.machine_st.registers[1]);
            }
            _ => {
                unreachable!();
            }
        }
    }

    #[inline(always)]
    pub(crate) fn shell(&mut self) {
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

        let command = self.machine_st.value_to_str_like(
            self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]))
        ).unwrap();

        match env::var("SHELL") {
            Ok(value) => {
                let command = process::Command::new(&value)
                    .arg("-c")
                    .arg(command.as_str())
                    .status();
                command_result(&mut self.machine_st, command);
            }
            _ => {
                match env::var("COMSPEC") {
                    Ok(value) => {
                        let command = process::Command::new(&value)
                            .arg("/C")
                            .arg(command.as_str())
                            .status();
                        command_result(&mut self.machine_st, command);
                    }
                    _ => {
                        self.machine_st.fail = true;
                    }
                }
            }
        };
    }

    #[inline(always)]
    pub(crate) fn chars_base64(&mut self) -> CallResult {
        let padding = cell_as_atom!(self.machine_st.registers[3]);
        let charset = cell_as_atom!(self.machine_st.registers[4]);

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

        if self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1])).is_var() {
            let b64 = self.machine_st.value_to_str_like(self.machine_st.registers[2]).unwrap();
            let bytes = base64::decode_config(b64.as_str(), config);

            match bytes {
                Ok(bs) => {
                    let string = self.u8s_to_string(&bs);

                    unify!(self.machine_st, self.machine_st.registers[1], string);
                }
                _ => {
                    self.machine_st.fail = true;
                    return Ok(());
                }
            }
        } else {
            let mut bytes = vec![];
            for c in self.machine_st.value_to_str_like(self.machine_st.registers[1]).unwrap().as_str().chars() {
                bytes.push(c as u8);
            }

            let b64 = base64::encode_config(bytes, config);
            let string = self.u8s_to_string(&b64.as_bytes());

            unify!(self.machine_st, self.machine_st.registers[2], string);
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn load_library_as_stream(&mut self) -> CallResult {
        let library_name = cell_as_atom!(self.machine_st.store(self.machine_st.deref(
            self.machine_st.registers[1]
        )));

        use crate::machine::LIBRARIES;

        match LIBRARIES.borrow().get(library_name.as_str()) {
            Some(library) => {
                let lib_stream = Stream::from_static_string(library, &mut self.machine_st.arena);
                unify!(self.machine_st, stream_as_cell!(lib_stream), self.machine_st.registers[2]);

                let mut path_buf = machine::current_dir();

                path_buf.push("/lib");
                path_buf.push(library_name.as_str());

                let library_path_str = path_buf.to_str().unwrap();
                let library_path = self.machine_st.atom_tbl.build_with(library_path_str);

                self.machine_st.unify_atom(library_path, self.machine_st.registers[3]);
            }
            None => {
                let stub = functor_stub(atom!("load"), 1);
                let err = self.machine_st.existence_error(
                    ExistenceError::ModuleSource(ModuleSource::Library(library_name))
                );

                return Err(self.machine_st.error_form(err, stub));
            }
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn devour_whitespace(&mut self) -> CallResult {
        let stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices.stream_aliases,
            atom!("$devour_whitespace"),
            1,
        )?;

        match self.machine_st.devour_whitespace(stream) {
            Ok(false) => { // not at EOF.
            }
            _ => {
                self.machine_st.fail = true;
            }
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn is_sto_enabled(&mut self) {
        if self.machine_st.unify_fn as usize == MachineState::unify_with_occurs_check as usize {
            self.machine_st.unify_atom(atom!("true"), self.machine_st.registers[1]);
        } else if self.machine_st.unify_fn as usize
            == MachineState::unify_with_occurs_check_with_error as usize
        {
            self.machine_st.unify_atom(atom!("error"), self.machine_st.registers[1]);
        } else {
            self.machine_st.unify_atom(atom!("false"), self.machine_st.registers[1]);
        }
    }

    #[inline(always)]
    pub(crate) fn set_sto_as_unify(&mut self) {
        self.machine_st.unify_fn = MachineState::unify_with_occurs_check;
        self.machine_st.bind_fn = MachineState::bind_with_occurs_check_wrapper;
    }

    #[inline(always)]
    pub(crate) fn set_nsto_as_unify(&mut self) {
        self.machine_st.unify_fn = MachineState::unify;
        self.machine_st.bind_fn = MachineState::bind;
    }

    #[inline(always)]
    pub(crate) fn set_sto_with_error_as_unify(&mut self) {
        self.machine_st.unify_fn = MachineState::unify_with_occurs_check_with_error;
        self.machine_st.bind_fn = MachineState::bind_with_occurs_check_with_error_wrapper;
    }

    #[inline(always)]
    pub(crate) fn home_directory(&mut self) {
        let path = match dirs_next::home_dir() {
            Some(path) => path,
            None => {
                self.machine_st.fail = true;
                return;
            }
        };

        if path.is_dir() {
            if let Some(path) = path.to_str() {
                let path_string = put_complete_string(
                    &mut self.machine_st.heap,
                    path,
                    &mut self.machine_st.atom_tbl,
                );

                unify!(self.machine_st, self.machine_st.registers[1], path_string);
                return;
            }
        }

        self.machine_st.fail = true;
    }

    pub(crate) fn debug_hook(&mut self) {
    }

    #[inline(always)]
    pub(crate) fn pop_count(&mut self) {
        let number = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
        let pop_count = integer_as_cell!(match Number::try_from(number) {
            Ok(Number::Fixnum(n)) => {
                Number::Fixnum(Fixnum::build_with(n.get_num().count_ones() as i64))
            }
            Ok(Number::Integer(n)) => {
                Number::arena_from(n.count_ones().unwrap(), &mut self.machine_st.arena)
            }
            _ => {
                unreachable!()
            }
        });

        unify!(self.machine_st, self.machine_st.registers[2], pop_count);
    }

    pub(super) fn systemtime_to_timestamp(&mut self, system_time: SystemTime) -> Atom {
        let datetime: DateTime<Local> = system_time.into();

        let mut fstr = "[".to_string();
        const SPECIFIERS: [char; 19] = [
            'Y', 'm', 'd', 'H', 'M', 'S', 'y', 'b', 'B', 'a', 'A', 'w', 'u', 'U', 'W', 'j', 'D',
            'x', 'v',
        ];

        for spec in SPECIFIERS {
            fstr.push_str(&format!("'{}'=\"%{}\", ", spec, spec).to_string());
        }

        fstr.push_str("finis].");
        let s = datetime.format(&fstr).to_string();

        self.machine_st.atom_tbl.build_with(&s)
    }

    pub(super) fn string_encoding_bytes(&mut self, data_arg: HeapCellValue, encoding: Atom) -> Vec<u8> {
        let data = self.machine_st.value_to_str_like(data_arg).unwrap();

        match encoding {
            atom!("utf8") => data.as_str().bytes().collect(),
            atom!("octet") => data.as_str().chars().map(|c| c as u8).collect(),
            _ => {
                unreachable!()
            }
        }
    }

    pub(super) fn xml_node_to_term(&mut self, node: roxmltree::Node) -> HeapCellValue {
        if node.is_text() {
            put_complete_string(
                &mut self.machine_st.heap,
                node.text().unwrap(),
                &mut self.machine_st.atom_tbl,
            )
        } else {
            let mut avec = Vec::new();

            for attr in node.attributes() {
                let name = self.machine_st.atom_tbl.build_with(attr.name());
                let value = put_complete_string(
                    &mut self.machine_st.heap,
                    &attr.value(),
                    &mut self.machine_st.atom_tbl,
                );

                avec.push(str_loc_as_cell!(self.machine_st.heap.len()));

                self.machine_st.heap.push(atom_as_cell!(atom!("="), 2));
                self.machine_st.heap.push(atom_as_cell!(name));
                self.machine_st.heap.push(value);
            }

            let attrs = heap_loc_as_cell!(
                iter_to_heap_list(&mut self.machine_st.heap, avec.into_iter())
            );

            let mut cvec = Vec::new();

            for child in node.children() {
                cvec.push(self.xml_node_to_term(child));
            }

            let children = heap_loc_as_cell!(
                iter_to_heap_list(&mut self.machine_st.heap, cvec.into_iter())
            );

            let tag = self.machine_st.atom_tbl.build_with(node.tag_name().name());

            let result = str_loc_as_cell!(self.machine_st.heap.len());

            self.machine_st.heap.push(atom_as_cell!(atom!("element"), 3));
            self.machine_st.heap.push(atom_as_cell!(tag));
            self.machine_st.heap.push(attrs);
            self.machine_st.heap.push(children);

            result
        }
    }

    pub(super) fn html_node_to_term(&mut self, node: select::node::Node) -> HeapCellValue {
        match node.name() {
            None => {
                put_complete_string(
                    &mut self.machine_st.heap,
                    &node.text(),
                    &mut self.machine_st.atom_tbl,
                )
            }
            Some(name) => {
                let mut avec = Vec::new();

                for attr in node.attrs() {
                    let name = self.machine_st.atom_tbl.build_with(attr.0);
                    let value = put_complete_string(
                        &mut self.machine_st.heap,
                        &attr.1,
                        &mut self.machine_st.atom_tbl,
                    );

                    avec.push(str_loc_as_cell!(self.machine_st.heap.len()));

                    self.machine_st.heap.push(atom_as_cell!(atom!("="), 2));
                    self.machine_st.heap.push(atom_as_cell!(name));
                    self.machine_st.heap.push(value);
                }

                let attrs = heap_loc_as_cell!(
                    iter_to_heap_list(&mut self.machine_st.heap, avec.into_iter())
                );

                let mut cvec = Vec::new();

                for child in node.children() {
                    cvec.push(self.html_node_to_term(child));
                }

                let children = heap_loc_as_cell!(
                    iter_to_heap_list(&mut self.machine_st.heap, cvec.into_iter())
                );

                let tag = self.machine_st.atom_tbl.build_with(name);
                let result = str_loc_as_cell!(self.machine_st.heap.len());

                self.machine_st.heap.push(atom_as_cell!(atom!("element"), 3));
                self.machine_st.heap.push(atom_as_cell!(tag));
                self.machine_st.heap.push(attrs);
                self.machine_st.heap.push(children);

                result
            }
        }
    }

    pub(super) fn u8s_to_string(&mut self, data: &[u8]) -> HeapCellValue {
        let buffer = String::from_iter(data.iter().map(|b| *b as char));

        if buffer.len() == 0 {
            empty_list_as_cell!()
        } else {
            atom_as_cstr_cell!(self.machine_st.atom_tbl.build_with(&buffer))
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

