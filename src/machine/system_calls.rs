use base64::Engine;
use dashu::integer::{Sign, UBig};
use lazy_static::lazy_static;
use num_order::NumOrd;

use crate::arena::*;
use crate::atom_table::*;
#[cfg(feature = "ffi")]
use crate::ffi::*;
use crate::forms::*;
use crate::functor_macro::*;
use crate::heap_iter::*;
use crate::heap_print::*;
#[cfg(feature = "http")]
use crate::http::{HttpListener, HttpRequest, HttpRequestData, HttpResponse};
use crate::instructions::*;
use crate::machine;
use crate::machine::code_walker::*;
use crate::machine::copier::*;
use crate::machine::heap::*;
use crate::machine::machine_errors::*;
use crate::machine::machine_indices::*;
use crate::machine::machine_state::*;
use crate::machine::partial_string::*;
use crate::machine::stack::*;
use crate::machine::streams::*;
use crate::machine::{get_structure_index, Machine, VERIFY_ATTR_INTERRUPT_LOC};
use crate::parser::ast::*;
use crate::parser::char_reader::*;
use crate::parser::dashu::Integer;
use crate::parser::parser::*;
use crate::read::*;
use crate::types::*;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use ordered_float::OrderedFloat;

use fxhash::{FxBuildHasher, FxHasher};
use indexmap::IndexSet;

use std::cell::Cell;
use std::cmp::Ordering;
use std::convert::TryFrom;
use std::env;
#[cfg(feature = "ffi")]
use std::ffi::CString;
use std::fs;
use std::hash::{BuildHasher, BuildHasherDefault};
use std::io::{ErrorKind, Read, Write};
use std::iter::{once, FromIterator};
use std::mem;
#[cfg(feature = "http")]
use std::net::{SocketAddr, ToSocketAddrs};
use std::net::{TcpListener, TcpStream};
use std::num::NonZeroU32;
use std::process;
use std::process::Child;
use std::process::Stdio;
#[cfg(feature = "http")]
use std::str::FromStr;
#[cfg(feature = "http")]
use std::sync::{Arc, Condvar, Mutex};

use chrono::{offset::Local, DateTime};
#[cfg(not(target_arch = "wasm32"))]
use cpu_time::ProcessTime;
use std::time::{Duration, SystemTime};

#[cfg(feature = "repl")]
use crossterm::event::{read, Event, KeyCode, KeyEvent, KeyEventKind, KeyModifiers};
#[cfg(feature = "repl")]
use crossterm::terminal::{disable_raw_mode, enable_raw_mode};

use blake2::{Blake2b512, Blake2s256};
use ring::rand::{SecureRandom, SystemRandom};
use ring::{digest, hkdf, hmac, pbkdf2};

#[cfg(feature = "crypto-full")]
use ring::aead;
use ripemd::{Digest, Ripemd160};
use sha3::{Sha3_224, Sha3_256, Sha3_384, Sha3_512};

use crrl::{ed25519, secp256k1, x25519};

pub(crate) mod special_math;

#[cfg(feature = "tls")]
use native_tls::{Identity, TlsAcceptor, TlsConnector};

use base64;
use roxmltree;

#[cfg(feature = "http")]
use futures::future;
#[cfg(feature = "http")]
use reqwest::Url;
use tokio::runtime::Handle;
use tokio::task;
#[cfg(feature = "http")]
use warp::hyper::header::{HeaderName, HeaderValue};
#[cfg(feature = "http")]
use warp::hyper::{HeaderMap, Method};
#[cfg(feature = "http")]
use warp::{Buf, Filter};

use super::libraries;
use super::preprocessor::to_op_decl;
use super::preprocessor::to_op_decl_spec;

/// Represents the presence (or absence) of a `module:` prefix to predicates, used to
/// refer to predicates defined in a given `module` that haven't been imported
/// (through `use_module/1`) or exported.
///
/// On the Rust side, [`MachineState::strip_module`] splits a given [`HeapCellValue`] into
/// a pair of [`ModuleQuantification`] and `HeapCellValue`.
///
/// On the Prolog side, `strip_module(X, Y, Z)` is a wrapper around [`MachineState::strip_module`],
/// which takes care of splitting the `X = module:predicate` pair into `Y = module` and
/// `Z = predicate`. If no module prefix is present (ie. [`MachineState::strip_module`] returned
/// `Unspecified`), then `strip_module/3` calls `load_context(Y)`, unifying `Y` with the currently
/// loaded module (or `user`).
///
/// [`Machine::quantification_to_module_name`] provides a similar mechanism on the Rust side to
/// obtain the currently loaded module in the `Unspecified` case.
/// It also defaults to `user`, for instance if we are in the REPL.
#[derive(Debug)]
pub(crate) enum ModuleQuantification {
    Specified(HeapCellValue),
    Unspecified,
}

impl ModuleQuantification {
    fn to_functor(&self) -> Vec<FunctorElement> {
        match self {
            &ModuleQuantification::Specified(cell) => functor!(atom!("specified"), [cell(cell)]),
            ModuleQuantification::Unspecified => functor!(atom!("unspecified")),
        }
    }

    #[inline]
    fn specified(&self) -> Option<HeapCellValue> {
        match self {
            &ModuleQuantification::Specified(cell) => Some(cell),
            ModuleQuantification::Unspecified => None,
        }
    }
}

#[cfg(feature = "repl")]
pub(crate) fn get_key() -> KeyEvent {
    let key;
    enable_raw_mode().expect("failed to enable raw mode");
    loop {
        let key_ = read();
        if let Ok(Event::Key(key_)) = key_ {
            if key_.kind != KeyEventKind::Release {
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

fn pstr_segment_char_count_and_tail(heap: &Heap, pstr_loc: usize) -> (usize, usize) {
    let char_iter = heap.char_iter(pstr_loc);

    let mut char_count = 0;
    let mut byte_offset = 0;

    for c in char_iter {
        if c == '\u{0}' {
            break;
        }

        char_count += 1;
        byte_offset += c.len_utf8();
    }

    (char_count, Heap::pstr_tail_idx(pstr_loc + byte_offset))
}

fn pstr_segment_char_count_up_to(
    heap: &Heap,
    pstr_loc: usize,
    max_chars: usize,
) -> PStrSegmentCountResult {
    let mut char_iter = heap.char_iter(pstr_loc);
    let mut char_count = 0;
    let mut byte_offset = 0;

    if max_chars > 0 {
        for c in &mut char_iter {
            if c == '\u{0}' {
                break;
            }

            char_count += 1;
            byte_offset += c.len_utf8();

            if char_count >= max_chars {
                break;
            }
        }
    }

    if char_iter.next().is_some() {
        PStrSegmentCountResult::Mid {
            char_count,
            pstr_loc: pstr_loc + byte_offset,
        }
    } else {
        PStrSegmentCountResult::End {
            char_count,
            tail_loc: Heap::pstr_tail_idx(pstr_loc + byte_offset),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct BrentAlgState {
    pub hare: usize,
    pub tortoise: usize,
    pub power: usize,
    pub lam: usize,
    pub pstr_chars: usize,
    max_steps: i64,
}

impl BrentAlgState {
    pub fn new(hare: usize) -> Self {
        Self {
            hare,
            tortoise: hare,
            power: 1,
            lam: 0,
            pstr_chars: 0,
            max_steps: -1,
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
            return Some(CycleSearchResult::Cyclic { lambda: self.lam });
        } else {
            self.teleport_tortoise();
        }

        None
    }

    #[inline(always)]
    pub fn num_steps(&self) -> usize {
        self.lam + self.pstr_chars + self.power - 1
    }

    #[inline(always)]
    pub fn exhausted_max_steps(&self) -> bool {
        self.max_steps > -1 && self.num_steps() as i64 >= self.max_steps
    }

    pub fn to_result(mut self, heap: &Heap) -> CycleSearchResult {
        loop {
            read_heap_cell!(heap[self.hare],
                (HeapCellValueTag::PStrLoc) => {
                    // let (_pstr_loc, offset) = pstr_loc_and_offset(heap, l);
                    // let offset = offset.get_num() as usize;
                    let num_steps = self.num_steps();
                    return CycleSearchResult::PStrLocation { num_steps, pstr_loc: heap[self.hare] };
                }
                (HeapCellValueTag::Atom, (name, arity)) => {
                    return if name == atom!("[]") && arity == 0 {
                        CycleSearchResult::ProperList { num_steps: self.num_steps() }
                    } else {
                        let heap_loc = if arity > 0 {
                            str_loc_as_cell!(self.hare)
                        } else {
                            heap_loc_as_cell!(self.hare)
                        };

                        CycleSearchResult::NotList { num_steps: self.num_steps(), heap_loc }
                    };
                }
                (HeapCellValueTag::Str, s) => {
                    let (name, arity) = cell_as_atom_cell!(heap[s])
                        .get_name_and_arity();

                    return if name == atom!("[]") && arity == 0 {
                        CycleSearchResult::ProperList { num_steps: self.num_steps() }
                    } else {
                        CycleSearchResult::NotList {
                            num_steps: self.num_steps(),
                            heap_loc: heap[self.hare],
                        }
                    };
                }
                (HeapCellValueTag::Lis, l) => {
                    return CycleSearchResult::UntouchedList { num_steps: self.num_steps(), list_loc: l };
                }
                (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
                    if h == self.hare {
                        // let var = heap[self.hare].as_var().unwrap();
                        return CycleSearchResult::PartialList {
                            num_steps: self.num_steps(),
                            heap_loc: heap[self.hare],
                        };
                    } else {
                        self.hare = h;
                    }
                }
                _ => {
                    let heap_loc = heap_loc_as_cell!(self.hare);
                    return CycleSearchResult::NotList { num_steps: self.num_steps(), heap_loc };
                }
            );
        }
    }

    fn add_pstr_chars(&mut self, heap: &Heap, pstr_loc: usize) -> Option<CycleSearchResult> {
        let next_cell_loc;

        if self.max_steps == -1 {
            let num_chars;
            (num_chars, next_cell_loc) = pstr_segment_char_count_and_tail(heap, pstr_loc);
            self.pstr_chars += num_chars - 1;
        } else {
            let max_chars = self.max_steps as usize - self.num_steps();

            match pstr_segment_char_count_up_to(heap, pstr_loc, max_chars) {
                PStrSegmentCountResult::Mid {
                    char_count,
                    pstr_loc,
                } => {
                    self.pstr_chars += char_count;
                    return Some(CycleSearchResult::PStrLocation {
                        num_steps: self.num_steps(),
                        pstr_loc: pstr_loc_as_cell!(pstr_loc),
                    });
                }
                PStrSegmentCountResult::End {
                    char_count,
                    tail_loc,
                } => {
                    self.pstr_chars += char_count.saturating_sub(1);
                    next_cell_loc = tail_loc;
                }
            }
        }

        self.step(next_cell_loc)
    }

    #[inline(always)]
    fn cycle_step(&mut self, heap: &Heap) -> Option<CycleSearchResult> {
        loop {
            let value = heap[self.hare];

            read_heap_cell!(value,
                (HeapCellValueTag::PStrLoc, h) => {
                    return self.add_pstr_chars(heap, h);
                }
                (HeapCellValueTag::Lis, h) => {
                    return self.step(h+1);
                }
                (HeapCellValueTag::Str, s) => {
                    let (name, arity) = cell_as_atom_cell!(heap[s]).get_name_and_arity();

                    return if name == atom!(".") && arity == 2 {
                        self.step(s+2)
                    } else {
                        Some(CycleSearchResult::NotList { num_steps: self.num_steps(), heap_loc: value })
                    };
                }
                (HeapCellValueTag::Atom, (name, arity)) => {
                    debug_assert!(arity == 0);

                    return if name == atom!("[]") {
                        Some(CycleSearchResult::ProperList { num_steps: self.num_steps() })
                    } else {
                        Some(CycleSearchResult::NotList { num_steps: self.num_steps(), heap_loc: value })
                    };
                }
                (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
                    if self.hare == h {
                        return Some(CycleSearchResult::PartialList { num_steps: self.num_steps(), heap_loc: value });
                    }

                    self.hare = h;
                }
                _ => {
                    return Some(CycleSearchResult::NotList { num_steps: self.num_steps(), heap_loc: value });
                }
            );
        }
    }

    pub fn detect_cycles(heap: &Heap, value: HeapCellValue) -> CycleSearchResult {
        let mut char_count = 0;

        let hare = read_heap_cell!(value,
            (HeapCellValueTag::Lis, offset) => {
                offset+1
            }
            (HeapCellValueTag::PStrLoc, h) => {
                let tail_idx;
                (char_count, tail_idx) = pstr_segment_char_count_and_tail(heap, h);

                if heap[tail_idx] == empty_list_as_cell!() {
                    return CycleSearchResult::ProperList { num_steps: char_count };
                }

                char_count = char_count.saturating_sub(1);
                tail_idx
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(heap[s])
                    .get_name_and_arity();

                if name == atom!("[]") && arity == 0 {
                    return CycleSearchResult::EmptyList;
                } else if name == atom!(".") && arity == 2 {
                    s + 2
                } else {
                    return CycleSearchResult::NotList { num_steps: 0, heap_loc: value };
                }
            }
            (HeapCellValueTag::Atom, (name, arity)) => {
                return if name == atom!("[]") && arity == 0 {
                    CycleSearchResult::EmptyList
                } else {
                    debug_assert_eq!(arity, 0);
                    CycleSearchResult::NotList { num_steps: 0, heap_loc: value }
                };
            }
            (HeapCellValueTag::AttrVar | HeapCellValueTag::StackVar | HeapCellValueTag::Var) => {
                return CycleSearchResult::PartialList { num_steps: 0, heap_loc: value };
            }
            _ => {
                return CycleSearchResult::NotList { num_steps: 0, heap_loc: value };
            }
        );

        let mut brent_st = BrentAlgState::new(hare);

        brent_st.power += 1; // advance a step.
        brent_st.pstr_chars = char_count;

        loop {
            if let Some(result) = brent_st.cycle_step(heap) {
                return result;
            }
        }
    }

    pub fn detect_cycles_with_max(
        heap: &Heap,
        max_steps: usize,
        value: HeapCellValue,
    ) -> CycleSearchResult {
        let mut char_count = 0;

        let hare = read_heap_cell!(value,
            (HeapCellValueTag::Lis, offset) => {
                if max_steps > 0 {
                    offset+1
                } else {
                    return CycleSearchResult::UntouchedList { num_steps: 0, list_loc: offset };
                }
            }
            (HeapCellValueTag::PStrLoc, h) => {
                match pstr_segment_char_count_up_to(heap, h, max_steps) {
                    PStrSegmentCountResult::Mid { char_count, pstr_loc } => {
                        let pstr_loc = pstr_loc_as_cell!(pstr_loc);
                        return CycleSearchResult::PStrLocation { num_steps: char_count, pstr_loc };
                    }
                    PStrSegmentCountResult::End { char_count: num_chars, tail_loc } => {
                        char_count = num_chars - 1;
                        tail_loc
                    }
                }
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(heap[s]).get_name_and_arity();

                if name == atom!("[]") && arity == 0 {
                    return CycleSearchResult::EmptyList;
                } else if name == atom!(".") && arity == 2 {
                    if max_steps > 0 {
                        s + 2
                    } else {
                        return CycleSearchResult::UntouchedList { num_steps: 0, list_loc: s + 1 };
                    }
                } else {
                    return CycleSearchResult::NotList { num_steps: 0, heap_loc: value };
                }
            }
            (HeapCellValueTag::Atom, (name, arity)) => {
                return if name == atom!("[]") && arity == 0 {
                    CycleSearchResult::EmptyList
                } else {
                    debug_assert_eq!(arity, 0);
                    CycleSearchResult::NotList { num_steps: 0, heap_loc: value }
                };
            }
            (HeapCellValueTag::AttrVar | HeapCellValueTag::StackVar | HeapCellValueTag::Var) => {
                return CycleSearchResult::PartialList { num_steps: 0, heap_loc: value };
            }
            _ => {
                return CycleSearchResult::NotList { num_steps: 0, heap_loc: value };
            }
        );

        let mut brent_st = BrentAlgState::new(hare);

        brent_st.power += 1; // advance a step.
        brent_st.pstr_chars = char_count;
        brent_st.max_steps = max_steps as i64;

        loop {
            if brent_st.exhausted_max_steps() {
                return brent_st.to_result(heap);
            }

            if let Some(result) = brent_st.cycle_step(heap) {
                return result;
            }
        }
    }
}

#[derive(Debug)]
enum MatchSite {
    NoMatchVarTail(usize), // no match, we refer to the location of the uninstantiated tail instead.
    Match(usize),          // a match
}

#[derive(Debug)]
enum PStrSegmentCountResult {
    Mid { char_count: usize, pstr_loc: usize },
    End { char_count: usize, tail_loc: usize },
}

#[derive(Debug)]
struct AttrListMatch {
    match_site: MatchSite,
    prev_tail: Option<usize>,
}

#[derive(Debug)]
pub(crate) struct FindallCopyInfo {
    offset: usize,
    pstr_threshold: usize,
}

impl MachineState {
    fn copy_lifted_heap_from_offset(&mut self, offset: usize, lh_offset: usize) {
        let reserve_size = self.lifted_heap.cell_len() - lh_offset;
        let mut writer = step_or_resource_error!(self, self.heap.reserve(reserve_size));

        writer.write_with(|section| {
            let mut lh_offset = lh_offset;

            while lh_offset + 4 < self.lifted_heap.cell_len() {
                let cell_threshold =
                    unsafe { self.lifted_heap[lh_offset + 3].to_fixnum_or_cut_point_unchecked() }
                        .get_num() as usize;
                let pstr_upper_threshold =
                    unsafe { self.lifted_heap[lh_offset + 4].to_fixnum_or_cut_point_unchecked() }
                        .get_num() as usize;

                for idx in lh_offset..cell_threshold {
                    section.push_cell(self.lifted_heap[idx] + offset);
                }

                let mut pstr_threshold = heap_index!(cell_threshold);

                while pstr_threshold < heap_index!(pstr_upper_threshold) {
                    let HeapStringScan { string, tail_idx } =
                        self.lifted_heap.scan_slice_to_str(pstr_threshold);

                    section.push_pstr(string);
                    section.push_cell(self.lifted_heap[tail_idx] + offset);

                    pstr_threshold = heap_index!(tail_idx + 1);
                }

                lh_offset = pstr_upper_threshold;
            }

            for idx in lh_offset..self.lifted_heap.cell_len() {
                section.push_cell(self.lifted_heap[idx] + offset);
            }
        });
    }

    #[inline(always)]
    pub(crate) fn unattributed_var(&mut self) {
        let attr_var = self.store(self.deref(self.registers[1]));

        if !attr_var.is_var() {
            self.fail = true;
            return;
        }

        read_heap_cell!(attr_var,
            (HeapCellValueTag::AttrVar, h) => {
                let list_cell = self.store(self.deref(self.heap[h+1]));
                self.fail = list_cell.get_tag() == HeapCellValueTag::Lis;
            }
            _ => {
            }
        );
    }

    pub(crate) fn get_attr_var_list(
        &mut self,
        attr_var: HeapCellValue,
    ) -> Result<Option<usize>, usize> {
        read_heap_cell!(attr_var,
            (HeapCellValueTag::AttrVar, h) => {
                Ok(Some(h + 1))
            }
            (HeapCellValueTag::Var | HeapCellValueTag::StackVar) => {
                // create an AttrVar in the heap.
                let h = self.heap.cell_len();
                let mut writer = self.heap.reserve(2)?;

                writer.write_with(|section| {
                    section.push_cell(attr_var_as_cell!(h));
                    section.push_cell(heap_loc_as_cell!(h+1));
                });

                self.bind(Ref::attr_var(h), attr_var);
                Ok(Some(h + 1))
            }
            _ => {
                Ok(None)
            }
        )
    }

    pub(crate) fn name_and_arity_from_heap(&self, cell: HeapCellValue) -> Option<PredicateKey> {
        read_heap_cell!(self.store(self.deref(cell)),
            (HeapCellValueTag::Str, s) => {
                Some(cell_as_atom_cell!(self.heap[s]).get_name_and_arity())
            }
            (HeapCellValueTag::Atom, (name, _arity)) => {
                Some((name, 0))
            }
            _ => {
                None
            }
        )
    }

    #[inline]
    pub(crate) fn variable_set<S: BuildHasher>(
        &mut self,
        seen_set: &mut IndexSet<HeapCellValue, S>,
        value: HeapCellValue,
    ) {
        let iter = eager_stackful_preorder_iter(&mut self.heap, value);

        for term in iter {
            if term.is_var() {
                seen_set.insert(term);
            }
        }
    }

    fn skip_max_list_cycle(&mut self, lam: usize) {
        fn step(heap: &Heap, mut value: HeapCellValue) -> usize {
            loop {
                read_heap_cell!(value,
                    (HeapCellValueTag::PStrLoc, h) => {
                        let HeapStringScan { tail_idx, .. } = heap.scan_slice_to_str(h);
                        return tail_idx;
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

        // let h = self.heap.cell_len();
        // self.heap.push(self.registers[3]);

        let orig_hare = step(&self.heap, self.registers[3]);
        let mut hare = orig_hare;
        let mut tortoise = hare;

        for _ in 0..lam {
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

        let mut brent_st = BrentAlgState::new(orig_hare);

        brent_st.cycle_step(&self.heap);

        while prev_hare != brent_st.hare {
            brent_st.cycle_step(&self.heap);
        }

        let target_n = self.store(self.deref(self.registers[1]));
        let num_steps = fixnum!(GInteger, brent_st.num_steps() as i64, &mut self.arena);

        self.unify_ginteger(num_steps, target_n);

        if !self.fail {
            unify!(self, self.registers[4], self.heap[prev_hare]);
        }
    }

    fn finalize_skip_max_list(&mut self, n: i64, value: HeapCellValue) {
        let target_n = self.store(self.deref(self.registers[1]));
        self.unify_fixnum(
            /* FIXME this is not safe */ unsafe { Fixnum::build_with_unchecked(n) },
            target_n,
        );

        if !self.fail {
            let xs = self.registers[4];
            unify!(self, value, xs);
        }
    }

    fn skip_max_list_result(&mut self, max_steps: i64) {
        let cell = self.store(self.deref(self.registers[3]));

        let search_result = if max_steps == -1 {
            BrentAlgState::detect_cycles(&self.heap, cell)
        } else {
            BrentAlgState::detect_cycles_with_max(&self.heap, max_steps as usize, cell)
        };

        match search_result {
            CycleSearchResult::PStrLocation {
                num_steps,
                pstr_loc,
            } => {
                let steps = if max_steps > -1 {
                    std::cmp::min(max_steps, num_steps as i64)
                } else {
                    max_steps
                };

                self.finalize_skip_max_list(steps, pstr_loc); // cell);
            }
            CycleSearchResult::UntouchedList {
                num_steps,
                list_loc: l,
            } => {
                self.finalize_skip_max_list(num_steps as i64, list_loc_as_cell!(l));
            }
            CycleSearchResult::EmptyList => {
                self.finalize_skip_max_list(0, empty_list_as_cell!());
            }
            CycleSearchResult::PartialList {
                num_steps,
                heap_loc,
            } => self.finalize_skip_max_list(num_steps as i64, heap_loc),
            CycleSearchResult::ProperList { num_steps } => {
                self.finalize_skip_max_list(num_steps as i64, empty_list_as_cell!())
            }
            CycleSearchResult::NotList {
                num_steps,
                heap_loc,
            } => {
                self.finalize_skip_max_list(num_steps as i64, heap_loc);
            }
            CycleSearchResult::Cyclic { lambda } => {
                self.skip_max_list_cycle(lambda);
            }
        };
    }

    pub fn skip_max_list(&mut self) -> CallResult {
        let max_steps = self.store(self.deref(self.registers[2]));
        let mut max_old = -1i64;

        if !max_steps.is_var() {
            let max_steps = Number::try_from((max_steps, &self.arena.f64_tbl));

            let max_steps_n = match max_steps {
                Ok(Number::Fixnum(n)) => Some(n.get_num()),
                Ok(Number::Integer(n)) => (&*n).try_into().ok(),
                _ => None,
            };

            if let Some(max_steps) = max_steps_n {
                if max_steps.unsigned_abs() <= 1 << 63 {
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
            self.heap[0] = term;
            let mut iter =
                stackful_post_order_iter::<NonListElider>(&mut self.heap, &mut self.stack, 0);

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

        let outcome = step_or_resource_error!(
            self,
            sized_iter_to_heap_list(&mut self.heap, seen_set.len(), seen_set.into_iter())
        );
        unify_fn!(*self, list_of_vars, outcome);
    }

    #[inline(always)]
    pub(crate) fn install_new_block(&mut self, value: HeapCellValue) -> usize {
        let value = self.store(self.deref(value));

        self.block = self.b;
        self.unify_fixnum(
            /* FIXME this is not safe */
            unsafe { Fixnum::build_with_unchecked(self.block as i64) },
            value,
        );

        self.block
    }

    pub(crate) fn copy_findall_solution(
        &mut self,
        lh_offset: usize,
        copy_target: HeapCellValue,
    ) -> Result<FindallCopyInfo, usize> {
        let threshold = self.lifted_heap.cell_len() - lh_offset;
        let mut writer = self.lifted_heap.reserve(5)?;

        writer.write_with(|section| {
            section.push_cell(list_loc_as_cell!(threshold + 1));
            section.push_cell(heap_loc_as_cell!(threshold + 5));
            section.push_cell(heap_loc_as_cell!(threshold + 2));
            section.push_cell(fixnum_as_cell!(Fixnum::build_with(0)));
            section.push_cell(fixnum_as_cell!(Fixnum::build_with(0)));
        });

        let old_lifted_cell_len = self.lifted_heap.cell_len();

        let copy_ball_term = CopyBallTerm::new(
            &mut self.attr_var_init.attr_var_queue,
            &mut self.stack,
            &mut self.heap,
            &mut self.lifted_heap,
        );

        let pstr_boundary = copy_term(copy_ball_term, copy_target, AttrVarPolicy::DeepCopy)?;

        Ok(FindallCopyInfo {
            offset: threshold + lh_offset + 2,
            pstr_threshold: pstr_boundary + old_lifted_cell_len,
        })
    }

    #[inline(always)]
    pub(crate) fn truncate_if_no_lifted_heap_diff(
        &mut self,
        addr_constr: impl Fn(usize) -> HeapCellValue,
    ) {
        read_heap_cell!(self.store(self.deref(self.registers[1])),
            (HeapCellValueTag::Fixnum, n) => {
                let lh_offset = n.get_num() as usize;

                if lh_offset >= self.lifted_heap.cell_len() {
                    self.lifted_heap.truncate(lh_offset);
                } else {
                    let threshold = self.lifted_heap.cell_len() - lh_offset;
                    step_or_resource_error!(
                        self,
                        self.lifted_heap.push_cell(addr_constr(threshold))
                    );
                }
            }
            _ => {
                self.fail = true;
            }
        );
    }

    pub(crate) fn parse_number_from_string(
        &mut self,
        string: &str,
        indices: &IndexStore,
        stub_gen: impl Fn() -> MachineStub,
    ) -> CallResult {
        use crate::parser::lexer::*;

        let nx = self.store(self.deref(self.registers[2]));
        let iter = std::io::Cursor::new(string);

        let mut lexer = Lexer::new(CharReader::new(iter), self);
        let mut tokens = vec![];

        match lexer.next_number_token() {
            Ok(token @ Token::Literal(Literal::Atom(atom!("-")))) => {
                tokens.push(token);

                if let Ok(token) = lexer.next_number_token() {
                    tokens.push(token);
                }
            }
            Ok(token) => {
                tokens.push(token);
            }
            Err(err) => {
                let err = self.syntax_error(err);
                return Err(self.error_form(err, stub_gen()));
            }
        }

        #[allow(clippy::never_loop)] // TODO why is there a loop here that never loops?
        loop {
            match lexer.lookahead_char() {
                Err(e) if e.is_unexpected_eof() => {
                    let mut parser = Parser::from_lexer(lexer);
                    let op_dir = CompositeOpDir::new(&indices.op_dir, None);

                    tokens.reverse();

                    match parser.read_term(&op_dir, Tokens::Provided(tokens)) {
                        Err(err) => {
                            let err = self.syntax_error(err);
                            return Err(self.error_form(err, stub_gen()));
                        }
                        Ok(Term::Literal(_, Literal::Rational(n))) => {
                            self.unify_rational(n, nx);
                        }
                        Ok(Term::Literal(_, Literal::F64(offset, _n))) => {
                            self.unify_f64(offset, nx);
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

                    return Ok(());
                }
                Ok(c) => {
                    let (line_num, col_num) = (lexer.line_num, lexer.col_num);

                    let err = ParserError::UnexpectedChar(c, line_num, col_num);
                    let err = self.syntax_error(err);

                    return Err(self.error_form(err, stub_gen()));
                }
                Err(_) => unreachable!(),
            }
        }
    }

    pub(crate) fn call_continuation_chunk(
        &mut self,
        chunk: HeapCellValue,
        return_p: usize,
    ) -> usize {
        let chunk = self.store(self.deref(chunk));

        let s = chunk.get_value() as usize;
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

        /*
        if num_cells > 0 {
            if let HeapCellValueTag::Fixnum = self.heap[s + 2].get_tag() {
                and_frame[1] = fixnum_as_cell!(Fixnum::build_with(self.b as i64));
            } else {
                and_frame[1] = self.heap[s + 2];
            }
        }
        */

        for index in s + 2..s + 2 + num_cells {
            if let HeapCellValueTag::CutPoint = self.heap[index].get_tag() {
                // adjust cut point to occur after call_continuation.
                and_frame[index - (s + 1)] = fixnum_as_cell!(
                    /* FIXME this is not safe */
                    unsafe { Fixnum::build_with_unchecked(self.b as i64) }.as_cutpoint()
                );
            } else {
                and_frame[index - (s + 1)] = self.heap[index];
            }
        }

        self.e = e;
        self.p
    }

    pub fn value_to_str_like(&mut self, value: HeapCellValue) -> Option<AtomOrString> {
        read_heap_cell!(value,
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
            _ => {
                if value.is_constant() {
                    return None;
                }

                // 0 is reserved for use by the machine. See
                // MachineState::new.
                self.heap[0] = value;

                let mut iter = HeapPStrIter::new(&self.heap, 0);
                let string = iter.to_string_mut();
                let end_cell = iter.heap[iter.focus()];

                // if the iteration doesn't terminate like a string
                // (i.e. with the [] atom or a CStr), it is not
                // "str_like" so return None.
                if end_cell.is_string_terminator(iter.heap) {
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
        stub_gen: impl Fn() -> MachineStub,
    ) -> Result<String, MachineStub> {
        let mut string = String::new();

        for addr in addrs {
            let addr = self.store(self.deref(addr));

            match Number::try_from((addr, &self.arena.f64_tbl)) {
                Ok(Number::Fixnum(n)) => {
                    if let Ok(n) = u32::try_from(n.get_num()) {
                        if let Some(c) = std::char::from_u32(n) {
                            string.push(c);
                            continue;
                        }
                    }
                }
                Ok(Number::Integer(n)) => {
                    let n: u32 = (&*n).try_into().unwrap();
                    if let Some(c) = std::char::from_u32(n) {
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
    ) -> (ModuleQuantification, HeapCellValue) {
        let mut module_quantification = ModuleQuantification::Unspecified;

        loop {
            read_heap_cell!(qualified_goal,
                (HeapCellValueTag::Str, s) => {
                    let (name, arity) = cell_as_atom_cell!(self.heap[s])
                        .get_name_and_arity();

                    if name == atom!(":") && arity == 2 {
                        let module_loc = self.heap[s+1];

                        module_quantification = ModuleQuantification::Specified(
                            module_loc,
                        );

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

        (module_quantification, qualified_goal)
    }
}

impl Machine {
    #[inline(always)]
    pub(crate) fn delete_all_attributes_from_var(&mut self) {
        let attr_var = self.deref_register(1);

        if let HeapCellValueTag::AttrVar = attr_var.get_tag() {
            let attr_var_loc = attr_var.get_value() as usize;
            self.machine_st.heap[attr_var_loc] = heap_loc_as_cell!(attr_var_loc);
            self.machine_st
                .trail(TrailRef::Ref(Ref::attr_var(attr_var_loc)));
        }
    }

    #[inline(always)]
    pub(crate) fn get_clause_p(&self, module_name: Atom) -> (usize, usize) {
        use crate::machine::loader::CompilationTarget;

        let key_cell = self.machine_st.registers[1];
        let key = self.machine_st.name_and_arity_from_heap(key_cell).unwrap();

        let compilation_target = if module_name == atom!("user") {
            CompilationTarget::User
        } else {
            CompilationTarget::Module(module_name)
        };

        let skeleton = self
            .indices
            .get_predicate_skeleton(&compilation_target, &key)
            .unwrap();

        let module_name = match compilation_target {
            CompilationTarget::User => atom!("builtins"),
            CompilationTarget::Module(target) => target,
        };

        let mut bp = self
            .indices
            .get_predicate_code_index(atom!("$clause"), 2, module_name)
            .and_then(|idx| {
                self.machine_st
                    .arena
                    .code_index_tbl
                    .get_entry(idx.into())
                    .local()
            })
            .unwrap();

        macro_rules! extract_ptr {
            ($ptr: expr) => {
                match $ptr {
                    IndexingCodePtr::External(p) => {
                        return (
                            skeleton.core.clause_clause_locs.back().cloned().unwrap(),
                            bp + p,
                        )
                    }
                    IndexingCodePtr::Internal(boip) => boip,
                    _ => unreachable!(),
                }
            };
        }

        loop {
            match &self.code[bp] {
                Instruction::IndexingCode(ref indexing_code) => {
                    let indexing_code_ptr = match &indexing_code[0] {
                        &IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(
                            _,
                            _,
                            c,
                            _,
                            s,
                        )) => {
                            if key.1 > 0 {
                                s
                            } else {
                                c
                            }
                        }
                        _ => {
                            unreachable!()
                        }
                    };

                    let boip = extract_ptr!(indexing_code_ptr);

                    let boip = match &indexing_code[boip] {
                        IndexingLine::Indexing(IndexingInstruction::SwitchOnStructure(ref hm)) => {
                            boip + extract_ptr!(hm.get(&key).cloned().unwrap())
                        }
                        IndexingLine::Indexing(IndexingInstruction::SwitchOnConstant(ref hm)) => {
                            boip + extract_ptr!(hm.get(&atom_as_cell!(key.0)).cloned().unwrap())
                        }
                        _ => boip,
                    };

                    match &indexing_code[boip] {
                        IndexingLine::IndexedChoice(indexed_choice) => {
                            let p = if self.machine_st.b > self.machine_st.e {
                                // this means the last
                                // self.machine_st.iip value has yet
                                // to be overwritten by the Trust
                                // instruction. In this case, return
                                // it.
                                self.machine_st.iip as usize
                            } else {
                                // otherwise, read the '$clause'
                                // choicepoint from the top of the
                                // stack. this is very volatile in
                                // that it depends on '$clause'
                                // immediately preceding
                                // '$get_clause_p', which cannot be
                                // the last clause of the retract
                                // helper to delay deallocation of its
                                // environment frame.
                                let clause_b = self.machine_st.stack.top();
                                self.machine_st.stack.index_or_frame(clause_b).prelude.biip as usize
                            };

                            return (
                                skeleton.core.clause_clause_locs[p],
                                bp + indexed_choice[p].offset(),
                            );
                        }
                        _ => unreachable!(),
                    }
                }
                &Instruction::RevJmpBy(offset) => {
                    bp -= offset;
                }
                _ => {
                    return (
                        skeleton.core.clause_clause_locs.back().cloned().unwrap(),
                        bp,
                    );
                }
            }
        }
    }

    #[inline(always)]
    pub(crate) fn deref_register(&self, i: usize) -> HeapCellValue {
        self.machine_st
            .store(self.machine_st.deref(self.machine_st.registers[i]))
    }

    fn quantification_to_module_name(
        &mut self,
        quantification: ModuleQuantification,
    ) -> Result<Atom, MachineError> {
        match quantification.specified() {
            Some(module_name) => {
                let module_name = self.machine_st.store(self.machine_st.deref(module_name));

                read_heap_cell!(module_name,
                    (HeapCellValueTag::Atom, (module_name, _arity)) => {
                        Ok(module_name)
                    }
                    (HeapCellValueTag::Var) => {
                        Err(self.machine_st.instantiation_error())
                    }
                    _ => {
                        Err(self.machine_st.type_error(ValidType::Atom, module_name))
                    }
                )
            }
            None => Ok(if let Some(load_context) = self.load_contexts.last() {
                load_context.module
            } else {
                atom!("user")
            }),
        }
    }

    #[inline(always)]
    pub(crate) fn fast_call(
        &mut self,
        arity: usize,
        call_at_index: impl Fn(&mut Machine, Atom, usize, IndexPtr) -> CallResult,
    ) -> CallResult {
        let load_registers = |machine_st: &mut MachineState,
                              goal: HeapCellValue,
                              goal_arity: usize| {
            read_heap_cell!(goal,
                (HeapCellValueTag::Str | HeapCellValueTag::Atom, s) => {
                    if goal_arity > 1 {
                        for idx in (1 .. arity + 1).rev() {
                            machine_st.registers[idx + goal_arity] = machine_st.registers[idx + 1];
                        }
                    } else if goal_arity == 0 {
                        for idx in 1 .. arity + 1 {
                            machine_st.registers[idx] = machine_st.registers[idx + 1];
                        }
                    }

                    for idx in 1 .. goal_arity + 1 {
                        machine_st.registers[idx] = machine_st.heap[s+idx];
                    }
                }
                _ => {
                    unreachable!()
                }
            )
        };

        let arity = arity - 1;
        let (mut module_quantification, mut goal) =
            self.machine_st.strip_module(self.machine_st.registers[1]);

        let (mut name, mut goal_arity, index_cell_opt) = read_heap_cell!(goal,
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.machine_st.heap[s])
                    .get_name_and_arity();

                (name, arity, get_structure_index(self.machine_st.heap[s.saturating_sub(1)]))
            }
            (HeapCellValueTag::Atom, (name, arity)) => {
                debug_assert_eq!(arity, 0);
                (name, arity, None)
            }
            _ => {
                self.machine_st.fail = true;
                return Ok(());
            }
        );

        let mut arity = arity + goal_arity;
        let mut module_name = self
            .quantification_to_module_name(module_quantification)
            .map_err(|err| {
                let stub = functor_stub(atom!("call"), arity);
                self.machine_st.error_form(err, stub)
            })?;

        let index_cell_opt = if index_cell_opt.is_some() {
            index_cell_opt
        } else {
            let is_internal_call = name == atom!("$call") && goal_arity > 0;

            if is_internal_call {
                debug_assert_eq!(goal.get_tag(), HeapCellValueTag::Str);
                goal = self.machine_st.heap[goal.get_value() as usize + 1];

                (module_quantification, goal) = self.machine_st.strip_module(goal);

                if let Some((inner_name, inner_arity)) =
                    self.machine_st.name_and_arity_from_heap(goal)
                {
                    module_name = self
                        .quantification_to_module_name(module_quantification)
                        .unwrap_or(module_name);

                    arity -= goal_arity;
                    (name, goal_arity) = (inner_name, inner_arity);
                    arity += goal_arity;

                    self.indices
                        .get_predicate_code_index(name, arity, module_name)
                } else {
                    None
                }
            } else if self
                .indices
                .goal_expansion_defined((name, arity), module_name)
            {
                None
            } else {
                self.indices
                    .get_predicate_code_index(name, arity, module_name)
            }
        };

        if let Some(code_idx) = index_cell_opt {
            let index_ptr = self
                .machine_st
                .arena
                .code_index_tbl
                .get_entry(code_idx.into());

            if !index_ptr.is_undefined() {
                load_registers(&mut self.machine_st, goal, goal_arity);
                self.machine_st.neck_cut();
                return call_at_index(self, name, arity, index_ptr);
            }
        }

        self.machine_st.fail = true;
        Ok(())
    }

    #[inline(always)]
    pub(crate) fn compile_inline_or_expanded_goal(&mut self) -> CallResult {
        let goal = self.deref_register(1);
        let module_name = self.deref_register(4);

        // supp_vars are the supplementary variables generated by
        // complete_partial_goal prior to goal_expansion.
        let mut supp_vars = IndexSet::with_hasher(FxBuildHasher::default());

        self.machine_st
            .variable_set(&mut supp_vars, self.machine_st.registers[2]);

        struct GoalAnalysisResult {
            index_ptr_loc: usize,
            is_simple_goal: bool,
            goal: HeapCellValue,
            key: PredicateKey,
            supp_vars: IndexSet<HeapCellValue, BuildHasherDefault<FxHasher>>,
        }

        let result = read_heap_cell!(goal,
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.machine_st.heap[s])
                    .get_name_and_arity();

                let mut expanded_vars = IndexSet::with_hasher(FxBuildHasher::default());

                // fill expanded_vars with variables of the partial
                // goal pre-completion by complete_partial_goal.
                for idx in s + 1 ..= s + arity - supp_vars.len() {
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
                    // expanded goal is not simple.

                    let post_supp_args = (s+arity-supp_vars.len()+1 ..= s+arity)
                        .map(|idx| self.machine_st.heap[idx]);

                    post_supp_args
                        .zip(supp_vars.iter())
                        .all(|(arg_term, supp_var)| {
                            let (quantification, arg_term) = self.machine_st.strip_module(arg_term);

                            let is_simple_module_quantification = match quantification {
                                ModuleQuantification::Unspecified => true,
                                ModuleQuantification::Specified(module_name) => {
                                    let module_name = self.machine_st.store(self.machine_st.deref(module_name));
                                    module_name == atom_as_cell!(atom!("user"))
                                }
                            };

                            if is_simple_module_quantification && arg_term.is_var() && supp_var.is_var() {
                                return arg_term == *supp_var;
                            }

                            false
                        }) && expanded_vars.intersection(&supp_vars).next().is_none()
                } else {
                    false
                };

                let (index_ptr_loc, goal) = if is_simple_goal {
                    let h = self.machine_st.heap.cell_len();
                    let arity = arity - supp_vars.len();

                    resource_error_call_result!(
                        self.machine_st,
                        self.machine_st.heap.push_cell(empty_list_as_cell!())
                    );

                    resource_error_call_result!(
                        self.machine_st,
                        self.machine_st.heap.copy_slice_to_end(
                            s ..= s + arity,
                        )
                    );

                    self.machine_st.heap[h+1] = atom_as_cell!(name, arity);

                    // even if arity == 0, goal must be a Str cell,
                    // since an index is about to appended to it.
                    (h, str_loc_as_cell!(h+1))
                } else {
                    (0, goal)
                };

                GoalAnalysisResult {
                    index_ptr_loc,
                    is_simple_goal,
                    goal,
                    key: (name, arity),
                    supp_vars
                }
            }
            (HeapCellValueTag::Atom, (name, arity)) => {
                debug_assert_eq!(arity, 0);

                let h = self.machine_st.heap.cell_len();

                let mut writer = resource_error_call_result!(
                    self.machine_st,
                    self.machine_st.heap.reserve(2)
                );

                writer.write_with(|section| {
                    section.push_cell(empty_list_as_cell!());
                    section.push_cell(goal);
                });

                GoalAnalysisResult {
                    index_ptr_loc: h,
                    is_simple_goal: true,
                    goal: str_loc_as_cell!(h+1),
                    key: (name, 0),
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
            self.machine_st.heap[result.index_ptr_loc] = HeapCellValue::from(idx);
            result.goal
        } else {
            let mut unexpanded_vars = IndexSet::with_hasher(FxBuildHasher::default());
            self.machine_st
                .variable_set(&mut unexpanded_vars, self.machine_st.registers[5]);

            // all supp_vars must appear later!
            let vars = IndexSet::<HeapCellValue, BuildHasherDefault<FxHasher>>::from_iter(
                unexpanded_vars.difference(&result.supp_vars).cloned(),
            );

            let vars: Vec<_> = vars
                .union(&result.supp_vars) // difference + union does not cancel.
                .map(|v| Term::Var(Cell::default(), VarPtr::from(format!("_{}", v.get_value()))))
                .collect();

            let helper_clause_loc = self.code.len();

            match self.compile_standalone_clause(temp_v!(1), &vars) {
                Err(e) => {
                    let err = self.machine_st.session_error(e);
                    let stub = functor_stub(atom!("call"), result.key.1);
                    return Err(self.machine_st.error_form(err, stub));
                }
                Ok(()) => {
                    let h = self.machine_st.heap.cell_len();
                    let mut writer = resource_error_call_result!(
                        self.machine_st,
                        self.machine_st.heap.reserve(unexpanded_vars.len() + 2)
                    );

                    let idx = CodeIndex::new(
                        IndexPtr::index(helper_clause_loc),
                        &mut self.machine_st.arena.code_index_tbl,
                    );

                    writer.write_with(|section| {
                        section.push_cell(HeapCellValue::from(idx));
                        section.push_cell(atom_as_cell!(atom!("$aux"), 0));

                        for value in unexpanded_vars.difference(&result.supp_vars).cloned() {
                            section.push_cell(value);
                        }
                    });

                    let anon_str_arity = self.machine_st.heap.cell_len() - h - 2;
                    self.machine_st.heap[h + 1] = atom_as_cell!(atom!("$aux"), anon_str_arity);

                    str_loc_as_cell!(h + 1)
                }
            }
        };

        let truncated_goal = self.machine_st.registers[3];
        unify!(&mut self.machine_st, expanded_term, truncated_goal);

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn is_expanded_or_inlined(&self) -> bool {
        let (_quantification, qualified_goal) =
            self.machine_st.strip_module(self.machine_st.registers[1]);

        if HeapCellValueTag::Str == qualified_goal.get_tag() {
            let s = qualified_goal.get_value() as usize;
            let name = cell_as_atom_cell!(self.machine_st.heap[s]).get_name();

            if name == atom!("$call") {
                return false;
            }

            let idx_cell = self.machine_st.heap[s.saturating_sub(1)];

            if HeapCellValueTag::CodeIndexOffset == idx_cell.get_tag() {
                return true;
            }
        }

        false
    }

    #[inline(always)]
    pub(crate) fn strip_module(&mut self) {
        let (module_quantification, qualified_goal) =
            self.machine_st.strip_module(self.machine_st.registers[1]);

        let target_module_loc = self.machine_st.registers[2];

        let functor_stub = module_quantification.to_functor();
        let mut functor_writer = Heap::functor_writer(functor_stub);

        let cell = functor_writer(&mut self.machine_st.heap).unwrap();
        unify_fn!(&mut self.machine_st, cell, target_module_loc);

        if !self.machine_st.fail {
            let target_qualified_goal = self.machine_st.registers[3];
            unify_fn!(&mut self.machine_st, qualified_goal, target_qualified_goal);
        }
    }

    #[inline(always)]
    pub(crate) fn prepare_call_clause(&mut self, arity: usize) -> CallResult {
        let qualified_goal = self.deref_register(2);

        // the first two arguments don't belong to the containing call/N.
        let arity = arity - 2;

        let (name, narity, s) = self
            .machine_st
            .setup_call_n_init_goal_info(qualified_goal, arity)?;

        // assemble goal from pre-loaded (narity) and supplementary
        // (arity) arguments.

        let target_goal = if arity == 0 {
            qualified_goal
        } else {
            let h = self.machine_st.heap.cell_len();

            let mut writer = resource_error_call_result!(
                self.machine_st,
                self.machine_st.heap.reserve(1 + narity + arity)
            );

            writer.write_with(|section| {
                section.push_cell(atom_as_cell!(name, narity + arity));

                for idx in 1..narity + 1 {
                    section.push_cell(section[s + idx]);
                }

                for idx in 1..arity + 1 {
                    section.push_cell(self.machine_st.registers[2 + idx]);
                }
            });

            if narity + arity > 0 {
                str_loc_as_cell!(h)
            } else {
                heap_loc_as_cell!(h)
            }
        };

        let target_qualified_goal = self.machine_st.registers[1];
        unify_fn!(&mut self.machine_st, target_goal, target_qualified_goal);
        Ok(())
    }

    #[inline(always)]
    pub(crate) fn dynamic_module_resolution(
        &mut self,
        narity: usize,
    ) -> Result<(Atom, PredicateKey), MachineStub> {
        let module_name = self.deref_register(1);

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
            _ => {
                let goal = self.machine_st.registers[2];
                let mut functor_writer = Heap::functor_writer(
                    functor!(atom!(":"), [cell(module_name), cell(goal)]),
                );

                let goal = resource_error_call_result!(
                    self.machine_st,
                    functor_writer(&mut self.machine_st.heap)
                );

                let err  = self.machine_st.type_error(ValidType::Callable, goal);
                let stub = functor_stub(atom!("call"), narity + 1);

                return Err(self.machine_st.error_form(err, stub));
            }
        );

        let goal = self.deref_register(2);

        let (name, arity, s) = self.machine_st.setup_call_n_init_goal_info(goal, narity)?;

        // TODO: think we just need the 'Greater' branch here.
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
    pub(crate) fn is_reset_cont_marker(&self, p: usize) -> bool {
        matches!(
            &self.code[p],
            &Instruction::CallResetContinuationMarker
                | &Instruction::ExecuteResetContinuationMarker
        )
    }

    #[inline(always)]
    pub(crate) fn bind_from_register(&mut self) {
        let reg = self.deref_register(2);
        let n = match Number::try_from((reg, &self.machine_st.arena.f64_tbl)) {
            Ok(Number::Fixnum(n)) => usize::try_from(n.get_num()).ok(),
            Ok(Number::Integer(n)) => {
                let value: usize = (&*n).try_into().unwrap();
                Some(value)
            }
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

    #[cfg(all(not(target_arch = "wasm32"), feature = "hostname"))]
    #[inline(always)]
    pub(crate) fn current_hostname(&mut self) {
        if let Ok(host) = hostname::get() {
            if let Some(host) = host.to_str() {
                let hostname = AtomTable::build_with(&self.machine_st.atom_tbl, host);

                let a1 = self.deref_register(1);
                self.machine_st.unify_atom(hostname, a1);

                return;
            }
        }

        self.machine_st.fail = true;
    }

    #[cfg(any(target_arch = "wasm32", not(feature = "hostname")))]
    pub(crate) fn current_hostname(&mut self) {
        unimplemented!()
    }

    #[inline(always)]
    pub(crate) fn current_input(&mut self) -> CallResult {
        let addr = self.deref_register(1);
        let stream = self.user_input;

        if let Some(var) = addr.as_var() {
            self.machine_st.bind(var, stream.into());
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
        let addr = self.deref_register(1);
        let stream = self.user_output;

        if let Some(var) = addr.as_var() {
            self.machine_st.bind(var, stream.into());
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
        if let Some(dir) = self.machine_st.value_to_str_like(self.deref_register(1)) {
            let str = dir.as_str();
            let path = std::path::Path::new(&*str);
            let mut files = Vec::new();

            if let Ok(entries) = fs::read_dir(path) {
                for entry in entries {
                    if let Ok(entry) = entry {
                        if let Some(name) = entry.file_name().to_str() {
                            let file_string_cell = resource_error_call_result!(
                                self.machine_st,
                                self.machine_st.heap.allocate_cstr(name)
                            );

                            files.push(file_string_cell);
                            continue;
                        }
                    }

                    let stub = functor_stub(atom!("directory_files"), 2);
                    let err = self.machine_st.representation_error(RepFlag::Character);
                    let err = self.machine_st.error_form(err, stub);

                    return Err(err);
                }

                let files_list_cell = resource_error_call_result!(
                    self.machine_st,
                    sized_iter_to_heap_list(
                        &mut self.machine_st.heap,
                        files.len(),
                        files.into_iter()
                    )
                );

                unify!(
                    self.machine_st,
                    self.machine_st.registers[2],
                    files_list_cell
                );
                return Ok(());
            }
        }

        self.machine_st.fail = true;
        Ok(())
    }

    #[inline(always)]
    pub(crate) fn file_size(&mut self) {
        if let Some(file) = self.machine_st.value_to_str_like(self.deref_register(1)) {
            let len = Number::arena_from(
                fs::metadata(&*file.as_str()).unwrap().len(),
                &mut self.machine_st.arena,
            );

            match len {
                Number::Fixnum(n) => self
                    .machine_st
                    .unify_fixnum(n, self.machine_st.registers[2]),
                Number::Integer(n) => self
                    .machine_st
                    .unify_big_int(n, self.machine_st.registers[2]),
                _ => unreachable!(),
            }
        } else {
            self.machine_st.fail = true;
        }
    }

    #[inline(always)]
    pub(crate) fn file_exists(&mut self) {
        if let Some(file) = self.machine_st.value_to_str_like(self.deref_register(1)) {
            let file_str = file.as_str();

            if !std::path::Path::new(&*file_str).exists()
                || !fs::metadata(&*file_str).unwrap().is_file()
            {
                self.machine_st.fail = true;
            }
        } else {
            self.machine_st.fail = true;
        }
    }

    #[inline(always)]
    pub(crate) fn directory_exists(&mut self) {
        if let Some(dir) = self.machine_st.value_to_str_like(self.deref_register(1)) {
            let dir_str = dir.as_str();

            if !std::path::Path::new(&*dir_str).exists()
                || !fs::metadata(&*dir_str).unwrap().is_dir()
            {
                self.machine_st.fail = true;
            }
        } else {
            self.machine_st.fail = true;
        }
    }

    #[inline(always)]
    pub(crate) fn file_time(&mut self) {
        if let Some(file) = self.machine_st.value_to_str_like(self.deref_register(1)) {
            let which = cell_as_atom!(self.deref_register(2));

            if let Ok(md) = fs::metadata(&*file.as_str()) {
                if let Ok(time) = match which {
                    atom!("modification") => md.modified(),
                    atom!("access") => md.accessed(),
                    atom!("creation") => md.created(),
                    _ => {
                        unreachable!()
                    }
                } {
                    let chars_string = self.systemtime_to_timestamp(time);

                    let cstr_cell = step_or_resource_error!(
                        self.machine_st,
                        self.machine_st.heap.allocate_cstr(&chars_string)
                    );

                    unify!(self.machine_st, cstr_cell, self.machine_st.registers[3]);
                    return;
                }
            }
        }

        self.machine_st.fail = true;
    }

    #[inline(always)]
    pub(crate) fn directory_separator(&mut self) {
        self.machine_st
            .unify_char(std::path::MAIN_SEPARATOR, self.machine_st.registers[1]);
    }

    #[inline(always)]
    pub(crate) fn make_directory(&mut self) {
        if let Some(dir) = self.machine_st.value_to_str_like(self.deref_register(1)) {
            match fs::create_dir(&*dir.as_str()) {
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
        if let Some(dir) = self.machine_st.value_to_str_like(self.deref_register(1)) {
            match fs::create_dir_all(&*dir.as_str()) {
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
        if let Some(file) = self.machine_st.value_to_str_like(self.deref_register(1)) {
            match fs::remove_file(&*file.as_str()) {
                Ok(_) => {}
                _ => {
                    self.machine_st.fail = true;
                }
            }
        }
    }

    #[inline(always)]
    pub(crate) fn rename_file(&mut self) {
        if let Some(file) = self.machine_st.value_to_str_like(self.deref_register(1)) {
            if let Some(renamed) = self.machine_st.value_to_str_like(self.deref_register(2)) {
                if fs::rename(&*file.as_str(), &*renamed.as_str()).is_ok() {
                    return;
                }
            }
        }

        self.machine_st.fail = true;
    }

    #[inline(always)]
    pub(crate) fn file_copy(&mut self) {
        if let Some(file) = self.machine_st.value_to_str_like(self.deref_register(1)) {
            if let Some(copied) = self.machine_st.value_to_str_like(self.deref_register(2)) {
                if fs::copy(&*file.as_str(), &*copied.as_str()).is_ok() {
                    return;
                }
            }
        }

        self.machine_st.fail = true;
    }

    #[inline(always)]
    pub(crate) fn delete_directory(&mut self) {
        if let Some(dir) = self.machine_st.value_to_str_like(self.deref_register(1)) {
            match fs::remove_dir(&*dir.as_str()) {
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

            let current_string = resource_error_call_result!(
                self.machine_st,
                self.machine_st.heap.allocate_cstr(current)
            );

            unify!(
                self.machine_st,
                current_string,
                self.machine_st.registers[1]
            );

            if self.machine_st.fail {
                return Ok(());
            }

            let target = self.deref_register(2);

            if let Some(next) = self.machine_st.value_to_str_like(target) {
                if env::set_current_dir(std::path::Path::new(&*next.as_str())).is_ok() {
                    return Ok(());
                }
            }
        }

        self.machine_st.fail = true;
        Ok(())
    }

    #[inline(always)]
    pub(crate) fn path_canonical(&mut self) -> CallResult {
        if let Some(path) = self.machine_st.value_to_str_like(self.deref_register(1)) {
            if let Ok(canonical) = fs::canonicalize(&*path.as_str()) {
                let cs = match canonical.to_str() {
                    Some(s) => s,
                    _ => {
                        let stub = functor_stub(atom!("path_canonical"), 2);
                        let err = self.machine_st.representation_error(RepFlag::Character);
                        let err = self.machine_st.error_form(err, stub);

                        return Err(err);
                    }
                };

                let canonical_string = resource_error_call_result!(
                    self.machine_st,
                    self.machine_st.heap.allocate_cstr(cs)
                );

                unify!(
                    self.machine_st,
                    canonical_string,
                    self.machine_st.registers[2]
                );
                return Ok(());
            }
        }

        self.machine_st.fail = true;
        Ok(())
    }

    #[inline(always)]
    pub(crate) fn atom_chars(&mut self) {
        let a1 = self.deref_register(1);

        read_heap_cell!(a1,
            (HeapCellValueTag::Atom, (name, arity)) => {
                debug_assert_eq!(arity, 0);

                let cell = step_or_resource_error!(
                    self.machine_st,
                    self.machine_st.heap.allocate_cstr(&name.as_str())
                );

                unify!(self.machine_st, self.machine_st.registers[2], cell);
            }
            (HeapCellValueTag::Var | HeapCellValueTag::AttrVar | HeapCellValueTag::StackVar) => {
                let a2 = self.deref_register(2);

                if let Some(str_like) = self.machine_st.value_to_str_like(a2) {
                    let atom_cell = match str_like {
                        AtomOrString::Atom(atom) => {
                            atom_as_cell!(if atom == atom!("[]") {
                                AtomTable::build_with(&self.machine_st.atom_tbl, "")
                            } else {
                                atom
                            })
                        }
                        AtomOrString::String(string) => {
                            atom_as_cell!(AtomTable::build_with(&self.machine_st.atom_tbl, &string))
                        }
                    };

                    self.machine_st.bind(a1.as_var().unwrap(), atom_cell);
                    return;
                }

                self.machine_st.fail = true;
            }
            _ => {
                self.machine_st.fail = true;
            }
        );
    }

    #[inline(always)]
    pub(crate) fn atom_codes(&mut self) -> CallResult {
        let a1 = self.deref_register(1);

        read_heap_cell!(a1,
            /*
            (HeapCellValueTag::Char, c) => {
                let h = self.machine_st.heap.len();

                self.machine_st.heap.push(fixnum_as_cell!(Fixnum::build_with(u32::from(c))));
                self.machine_st.heap.push(empty_list_as_cell!());

                unify!(self.machine_st, list_loc_as_cell!(h), self.machine_st.registers[2]);
            }
            */
            (HeapCellValueTag::Atom, (name, arity)) => {
                debug_assert_eq!(arity, 0);

                let name = name.as_str();
                let iter = name.chars().map(|c| fixnum_as_cell!(Fixnum::build_with(c)));

                let list_cell = resource_error_call_result!(
                    self.machine_st,
                    sized_iter_to_heap_list(
                        &mut self.machine_st.heap,
                        name.chars().count(),
                        iter,
                    )
                );

                unify!(self.machine_st, list_cell, self.machine_st.registers[2]);
            }
            /*
            (HeapCellValueTag::Str, s) => {
                /*
                let (name, arity) = cell_as_atom_cell!(self.machine_st.heap[s])
                    .get_name_and_arity();

                if arity == 0 {
                    let name = name.as_str();
                    let iter = name.chars().map(|c| fixnum_as_cell!(Fixnum::build_with(c as i64)));

                    let list_cell = resource_error_call_result!(
                        self.machine_st,
                        sized_iter_to_heap_list(
                            &mut self.machine_st.heap,
                            name.as_str().chars().count(),
                            iter,
                        )
                    );

                    unify!(self.machine_st, list_cell, self.machine_st.registers[2]);
                } else {
                */
                self.machine_st.fail = true;
                // }
            }
            */
            (HeapCellValueTag::Var | HeapCellValueTag::AttrVar | HeapCellValueTag::StackVar) => {
                let stub_gen = || functor_stub(atom!("atom_codes"), 2);

                match self.machine_st.try_from_list(self.machine_st.registers[2], stub_gen) {
                    Ok(addrs) => {
                        let string = self.machine_st.codes_to_string(addrs.into_iter(), stub_gen)?;
                        let atom = AtomTable::build_with(&self.machine_st.atom_tbl, &string);

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
        let a1 = self.deref_register(1);

        let len: i64 = read_heap_cell!(a1,
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.machine_st.heap[s])
                    .get_name_and_arity();

                if arity == 0 {
                    name.as_str().chars().count() as i64
                } else {
                    self.machine_st.fail = true;
                    return;
                }
            }
            (HeapCellValueTag::Atom, (name, arity)) => {
                if arity == 0 {
                    name.as_str().chars().count() as i64
                } else {
                    self.machine_st.fail = true;
                    return;
                }
            }
            /*
            (HeapCellValueTag::Char) => {
                1
            }
            */
            _ => {
                unreachable!()
            }
        );

        let a2 = self.deref_register(2);
        self.machine_st.unify_fixnum(
            /* FIXME this is not safe */ unsafe { Fixnum::build_with_unchecked(len) },
            a2,
        );
    }

    #[inline(always)]
    pub(crate) fn call_continuation(&mut self, last_call: bool) -> CallResult {
        let stub_gen = || functor_stub(atom!("call_continuation"), 1);
        let a1 = self.deref_register(1);

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
        let a1 = self.deref_register(1);
        let atom_or_string = self.machine_st.value_to_str_like(a1).unwrap();

        self.machine_st
            .parse_number_from_string(&atom_or_string.as_str(), &self.indices, stub_gen)
    }

    #[inline(always)]
    pub(crate) fn create_partial_string(&mut self) {
        let a1 = self.deref_register(1);

        if let Some(str_like) = self.machine_st.value_to_str_like(a1) {
            let str = match str_like {
                AtomOrString::String(string) => string,
                _ => {
                    unreachable!()
                }
            };

            let pstr_loc_cell =
                step_or_resource_error!(self.machine_st, self.machine_st.heap.allocate_pstr(&str));

            let tail_loc = self.machine_st.heap.cell_len();

            step_or_resource_error!(
                self.machine_st,
                self.machine_st.heap.push_cell(heap_loc_as_cell!(tail_loc))
            );

            unify!(self.machine_st, self.machine_st.registers[2], pstr_loc_cell);

            if !self.machine_st.fail {
                let tail = self.machine_st.registers[3];
                unify!(self.machine_st, tail, heap_loc_as_cell!(tail_loc));
            }
        }
    }

    #[inline(always)]
    pub(crate) fn is_partial_string(&mut self) {
        let value = self.deref_register(1);

        if value.is_constant() {
            self.machine_st.fail = empty_list_as_cell!() != value;
        } else {
            self.machine_st.heap[0] = value;
            let mut iter = HeapPStrIter::new(&self.machine_st.heap, 0);

            for _ in iter.by_ref() {}

            let focus = iter.focus();
            let end_cell = self.machine_st.heap[focus];
            let at_end_of_pstr =
                end_cell.is_var() || end_cell.is_string_terminator(&self.machine_st.heap);

            self.machine_st.fail = !at_end_of_pstr;
        }
    }

    #[inline(always)]
    pub(crate) fn partial_string_tail(&mut self) {
        let pstr = self.deref_register(1);
        let a2 = self.deref_register(2);

        read_heap_cell!(pstr,
            (HeapCellValueTag::PStrLoc, h) => {
                let HeapStringScan { tail_idx, .. } = self.machine_st.heap.scan_slice_to_str(h);
                unify_fn!(self.machine_st, heap_loc_as_cell!(tail_idx), a2);
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
        let _guard = RawReadGuard::new();
        let stub_gen = || functor_stub(atom!("peek_byte"), 2);

        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices,
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
            return Ok(());
        }

        let addr = self.deref_register(2);

        if stream.at_end_of_stream() {
            self.machine_st.unify_fixnum(Fixnum::build_with(-1), addr);

            if self.machine_st.fail {
                self.machine_st.fail = false;
            } else {
                return Ok(());
            }
        }

        let addr = match addr {
            addr if addr.is_var() => addr,
            addr => match Number::try_from((addr, &self.machine_st.arena.f64_tbl)) {
                Ok(Number::Integer(n)) => {
                    let result: Result<u8, _> = (&*n).try_into();
                    if let Ok(value) = result {
                        fixnum_as_cell!(Fixnum::build_with(value))
                    } else {
                        let err = self.machine_st.type_error(ValidType::InByte, addr);
                        return Err(self.machine_st.error_form(err, stub_gen()));
                    }
                }
                Ok(Number::Fixnum(n)) => {
                    if let Ok(nb) = u8::try_from(n.get_num()) {
                        fixnum_as_cell!(Fixnum::build_with(nb))
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
                    self.machine_st.unify_fixnum(Fixnum::build_with(b), addr);
                    break;
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

                    if EOFAction::Reset != stream.options().eof_action() || self.machine_st.fail {
                        break;
                    }
                }
            }
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn peek_char(&mut self) -> CallResult {
        let _guard = RawReadGuard::new();
        let stub_gen = || functor_stub(atom!("peek_char"), 2);

        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices,
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

        if stream.past_end_of_stream()
            && (EOFAction::Reset != stream.options().eof_action() || self.machine_st.fail)
        {
            return Ok(());
        }

        let a2 = self.deref_register(2);

        if stream.at_end_of_stream() {
            let end_of_file = atom!("end_of_file");

            self.machine_st.unify_atom(end_of_file, a2);

            return Ok(());
        }

        let a2 = read_heap_cell!(a2,
            /*
            (HeapCellValueTag::Char) => {
                a2
            }
            */
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
            match stream
                .peek_char()
                .map(|result| result.map_err(|e| e.kind()))
            {
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

                    if EOFAction::Reset != stream.options().eof_action() || self.machine_st.fail {
                        break;
                    }
                }
            }
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn peek_code(&mut self) -> CallResult {
        let _guard = RawReadGuard::new();
        let stub_gen = || functor_stub(atom!("peek_code"), 2);

        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices,
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

        if stream.past_end_of_stream()
            && (EOFAction::Reset != stream.options().eof_action() || self.machine_st.fail)
        {
            return Ok(());
        }

        let a2 = self.deref_register(2);

        if stream.at_end_of_stream() {
            self.machine_st.unify_fixnum(Fixnum::build_with(-1), a2);

            if self.machine_st.fail {
                self.machine_st.fail = false;
            } else {
                return Ok(());
            }
        }

        let addr = read_heap_cell!(a2,
            (HeapCellValueTag::Var | HeapCellValueTag::StackVar | HeapCellValueTag::AttrVar) => {
                a2
            }
            _ => {
                match Number::try_from((a2, &self.machine_st.arena.f64_tbl)) {
                    Ok(Number::Integer(n)) => {
                        let n: u32 = (&*n).try_into().unwrap();

                        if std::char::from_u32(n).is_some() {
                            fixnum_as_cell!(Fixnum::build_with(n))
                        } else {
                            let err = self.machine_st.representation_error(RepFlag::InCharacterCode);
                            return Err(self.machine_st.error_form(err, stub_gen()));
                        }
                    }
                    Ok(Number::Fixnum(n)) => {
                        let n = u32::try_from(n.get_num())
                            .ok()
                            .and_then(|n| std::char::from_u32(n).map(|_| n));

                        if let Some(n) = n {
                            fixnum_as_cell!(Fixnum::build_with(n))
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
                    self.machine_st
                        .unify_fixnum(Fixnum::build_with(u32::from(c)), addr);
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

                    if EOFAction::Reset != stream.options().eof_action() || self.machine_st.fail {
                        break;
                    }
                }
            }
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn number_to_chars(&mut self) {
        let n = self.deref_register(1);
        let chs = self.deref_register(2);

        let string = match Number::try_from((n, &self.machine_st.arena.f64_tbl)) {
            Ok(Number::Float(OrderedFloat(n))) => fmt_float(n),
            Ok(Number::Fixnum(n)) => n.get_num().to_string(),
            Ok(Number::Integer(n)) => n.to_string(),
            Ok(Number::Rational(r)) => {
                // n has already been confirmed as an integer, and
                // internally, Rational is assumed reduced, so its denominator
                // must be 1.
                r.numerator().to_string()
            }
            _ => {
                unreachable!()
            }
        };

        let cstr_cell = step_or_resource_error!(
            self.machine_st,
            self.machine_st.heap.allocate_cstr(string.trim())
        );

        unify!(self.machine_st, cstr_cell, chs);
    }

    #[inline(always)]
    pub(crate) fn number_to_codes(&mut self) {
        let n = self.deref_register(1);
        let chs = self.machine_st.registers[2];

        let string = match Number::try_from((n, &self.machine_st.arena.f64_tbl)) {
            Ok(Number::Float(OrderedFloat(n))) => {
                format!("{n:<20?}")
            }
            Ok(Number::Fixnum(n)) => n.get_num().to_string(),
            Ok(Number::Integer(n)) => n.to_string(),
            Ok(Number::Rational(r)) => {
                // n has already been confirmed as an integer, and
                // internally, Rational is assumed reduced, so its
                // denominator must be 1.
                r.numerator().to_string()
            }
            _ => {
                unreachable!()
            }
        };

        let codes = string
            .trim()
            .chars()
            .map(|c| fixnum_as_cell!(Fixnum::build_with(u32::from(c))));

        let list_cell = step_or_resource_error!(
            self.machine_st,
            sized_iter_to_heap_list(
                &mut self.machine_st.heap,
                string.trim().chars().count(),
                codes,
            )
        );

        unify!(self.machine_st, list_cell, chs);
    }

    #[inline(always)]
    pub(crate) fn codes_to_number(&mut self) -> CallResult {
        let stub_gen = || functor_stub(atom!("number_codes"), 2);

        match self
            .machine_st
            .try_from_list(self.machine_st.registers[1], stub_gen)
        {
            Err(e) => {
                return Err(e);
            }
            Ok(addrs) => {
                let string = self
                    .machine_st
                    .codes_to_string(addrs.into_iter(), stub_gen)?;
                self.machine_st.parse_number_from_string(
                    string.as_str(),
                    &self.indices,
                    stub_gen,
                )?;
            }
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn lifted_heap_length(&mut self) {
        let a1 = self.machine_st.registers[1];
        /* FIXME this is not safe */
        let lh_len =
            unsafe { Fixnum::build_with_unchecked(self.machine_st.lifted_heap.cell_len() as i64) };

        self.machine_st.unify_fixnum(lh_len, a1);
    }

    #[inline(always)]
    pub(crate) fn char_code(&mut self) -> CallResult {
        let stub_gen = || functor_stub(atom!("char_code"), 2);
        let a1 = self.deref_register(1);
        let a2 = self.deref_register(2);

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
            _ => {
                match Number::try_from((a2, &self.machine_st.arena.f64_tbl)) {
                    Ok(Number::Integer(n)) => {
                        let n: u32 = (&*n).try_into().unwrap();
                        let n = std::char::from_u32(n);
                        let c = match n {
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
                        if let Ok(n) = u32::try_from(n.get_num()) {
                            if let Some(c) = std::char::from_u32(n) {
                                self.machine_st.unify_char(c, a1);
                                return Ok(());
                            }
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

        self.machine_st
            .unify_fixnum(Fixnum::build_with(u32::from(c)), a2);

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn char_type(&mut self) {
        let a1 = self.deref_register(1);
        let a2 = self.deref_register(2);

        let c = read_heap_cell!(a1,
            /*
            (HeapCellValueTag::Char, c) => {
                c
            }
            */
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

        read_heap_cell!(a2,
            (HeapCellValueTag::Atom, (chars, _arity)) => {
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
                method_check!(is_ascii_punctuation, atom!("ascii_punctuation"));
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
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.machine_st.heap[s])
                    .get_name_and_arity();

                match (name, arity) {
                    (atom!("upper"), 1) => {
                        let reg = self.machine_st.deref(self.machine_st.heap[s+1]);
                        let upper_str = step_or_resource_error!(
                            self.machine_st,
                            self.machine_st.heap.allocate_cstr(&c.to_uppercase().to_string())
                        );
                        unify!(self.machine_st, reg, upper_str);
                    }
                    (atom!("lower"), 1) => {
                        let reg = self.machine_st.deref(self.machine_st.heap[s+1]);
                        let lower_str = step_or_resource_error!(
                            self.machine_st,
                            self.machine_st.heap.allocate_cstr(&c.to_uppercase().to_string())
                        );

                        unify!(self.machine_st, reg, lower_str);
                    }
                    _ => {
                        unreachable!()
                    }
                }
            }
            _ => {
                unreachable!()
            }
        );
    }

    #[inline(always)]
    pub(crate) fn check_cut_point(&mut self) {
        let addr = self.deref_register(1);
        let old_b = unsafe { addr.to_fixnum_or_cut_point_unchecked() }.get_num() as usize;

        let prev_b = self
            .machine_st
            .stack
            .index_or_frame(self.machine_st.b)
            .prelude
            .b;
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
        let key = cell_as_atom!(self.deref_register(1));
        let addr = self.machine_st.registers[2];

        match self.indices.global_variables.get_mut(&key) {
            Some((ref ball, ref mut loc)) => match loc {
                Some(value_loc) => {
                    unify_fn!(self.machine_st, addr, *value_loc);
                }
                None if !ball.stub.is_empty() => {
                    let h = step_or_resource_error!(
                        self.machine_st,
                        ball.copy_and_align_to(&mut self.machine_st.heap)
                    );

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
            &self.indices,
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
        let addr = self.deref_register(2);

        if addr.is_var() {
            let err = self.machine_st.instantiation_error();
            Err(self.machine_st.error_form(err, stub_gen()))
        } else {
            match Number::try_from((addr, &self.machine_st.arena.f64_tbl)) {
                Ok(Number::Integer(n)) => {
                    let n: u32 = (&*n).try_into().unwrap();
                    let n = char::try_from(n);
                    if let Ok(c) = n {
                        write!(&mut stream, "{c}").unwrap();
                        return Ok(());
                    }
                }
                Ok(Number::Fixnum(n)) => {
                    let n = n.get_num();

                    if let Some(c) = u32::try_from(n).ok().and_then(char::from_u32) {
                        write!(&mut stream, "{c}").unwrap();
                        return Ok(());
                    }
                }
                _ => {
                    let err = self.machine_st.type_error(ValidType::Integer, addr);
                    return Err(self.machine_st.error_form(err, stub_gen()));
                }
            }

            let err = self.machine_st.representation_error(RepFlag::CharacterCode);
            Err(self.machine_st.error_form(err, stub_gen()))
        }
    }

    #[inline(always)]
    pub(crate) fn put_char(&mut self) -> CallResult {
        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices,
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
        let addr = self.deref_register(2);

        if addr.is_var() {
            let err = self.machine_st.instantiation_error();
            Err(self.machine_st.error_form(err, stub_gen()))
        } else {
            read_heap_cell!(addr,
                (HeapCellValueTag::Atom, (name, _arity)) => {
                    if let Some(c) = name.as_char() {
                        write!(&mut stream, "{c}").unwrap();
                        return Ok(());
                    }
                }
                /*
                (HeapCellValueTag::Char, c) => {
                    write!(&mut stream, "{c}").unwrap();
                    return Ok(());
                }
                */
                _ => {
                }
            );

            let err = self.machine_st.type_error(ValidType::Character, addr);
            Err(self.machine_st.error_form(err, stub_gen()))
        }
    }

    #[inline(always)]
    pub(crate) fn put_chars(&mut self) -> CallResult {
        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices,
            atom!("$put_chars"),
            2,
        )?;

        let mut bytes = Vec::new();
        let stub_gen = || functor_stub(atom!("$put_chars"), 2);

        if let Some(string) = self
            .machine_st
            .value_to_str_like(self.machine_st.registers[2])
        {
            if stream.options().stream_type() == StreamType::Binary {
                for c in string.as_str().chars() {
                    if c as u32 > 255 {
                        let err = self
                            .machine_st
                            .type_error(ValidType::Byte, char_as_cell!(c));
                        return Err(self.machine_st.error_form(err, stub_gen()));
                    }

                    bytes.push(c as u8);
                }
            } else {
                bytes = string.as_str().bytes().collect();
            }

            match stream.write_all(&bytes) {
                Ok(_) => {}
                _ => {
                    let addr = stream.into();
                    let err = self
                        .machine_st
                        .existence_error(ExistenceError::Stream(addr));

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
            &self.indices,
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
        let addr = self.deref_register(2);

        if addr.is_var() {
            let err = self.machine_st.instantiation_error();
            return Err(self.machine_st.error_form(err, stub_gen()));
        } else {
            match Number::try_from((addr, &self.machine_st.arena.f64_tbl)) {
                Ok(Number::Integer(n)) => {
                    let n: u8 = (&*n).try_into().unwrap();

                    match stream.write(&[n]) {
                        Ok(1) => {
                            return Ok(());
                        }
                        _ => {
                            let err = self
                                .machine_st
                                .existence_error(ExistenceError::Stream(stream.into()));

                            return Err(self.machine_st.error_form(err, stub_gen()));
                        }
                    }
                }
                Ok(Number::Fixnum(n)) => {
                    if let Ok(nb) = u8::try_from(n.get_num()) {
                        match stream.write(&[nb]) {
                            Ok(1) => {
                                return Ok(());
                            }
                            _ => {
                                let err = self
                                    .machine_st
                                    .existence_error(ExistenceError::Stream(stream.into()));

                                return Err(self.machine_st.error_form(err, stub_gen()));
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        let err = self
            .machine_st
            .type_error(ValidType::Byte, self.machine_st.registers[2]);
        Err(self.machine_st.error_form(err, stub_gen()))
    }

    #[inline(always)]
    pub(crate) fn get_byte(&mut self) -> CallResult {
        let _guard = RawReadGuard::new();
        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices,
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
            self.machine_st.eof_action(
                self.machine_st.registers[2],
                stream,
                atom!("get_byte"),
                2,
            )?;

            if EOFAction::Reset != stream.options().eof_action() || self.machine_st.fail {
                return Ok(());
            }
        }

        let stub_gen = || functor_stub(atom!("get_byte"), 2);
        let addr = self.deref_register(2);

        let addr = if addr.is_var() {
            addr
        } else {
            match Number::try_from((addr, &self.machine_st.arena.f64_tbl)) {
                Ok(Number::Integer(ref n)) if (**n).num_eq(&1_i64) => {
                    fixnum_as_cell!(Fixnum::build_with(-1))
                }
                Ok(Number::Fixnum(n)) if n.get_num() == -1_i64 => {
                    fixnum_as_cell!(Fixnum::build_with(-1))
                }
                Ok(Number::Integer(n)) => {
                    let n: Result<u8, _> = (&*n).try_into();

                    if let Ok(value) = n {
                        fixnum_as_cell!(Fixnum::build_with(value))
                    } else {
                        let err = self.machine_st.type_error(ValidType::InByte, addr);
                        return Err(self.machine_st.error_form(err, stub_gen()));
                    }
                }
                Ok(Number::Fixnum(n)) => {
                    if let Ok(nb) = u8::try_from(n.get_num()) {
                        fixnum_as_cell!(Fixnum::build_with(nb))
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

        let mut b = [0u8; 1];

        match stream.read(&mut b) {
            Ok(1) => {
                self.machine_st.unify_fixnum(Fixnum::build_with(b[0]), addr);
            }
            _ => {
                stream.set_past_end_of_stream(true);
                self.machine_st
                    .unify_fixnum(Fixnum::build_with(-1), self.machine_st.registers[2]);
            }
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn get_char(&mut self) -> CallResult {
        let _guard = RawReadGuard::new();
        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices,
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

        if stream.past_end_of_stream()
            && (EOFAction::Reset != stream.options().eof_action() || self.machine_st.fail)
        {
            return Ok(());
        }

        let addr = self.deref_register(2);

        if stream.at_end_of_stream() {
            let end_of_file = atom!("end_of_file");
            stream.set_past_end_of_stream(true);

            self.machine_st.unify_atom(end_of_file, addr);

            return Ok(());
        } else if addr == atom_as_cell!(atom!("end_of_file")) {
            self.machine_st.fail = true;
            return Ok(());
        }

        let stub_gen = || functor_stub(atom!("get_char"), 2);

        let addr = if addr.is_var() {
            addr
        } else {
            read_heap_cell!(addr,
                (HeapCellValueTag::Atom, (atom, _arity)) => {
                    debug_assert!(atom.as_char().is_some());
                    addr
                }
                _ => {
                    let err = self.machine_st.type_error(ValidType::InCharacter, addr);
                    return Err(self.machine_st.error_form(err, stub_gen()));
                }
            )
        };

        let mut iter = match self.machine_st.open_parsing_stream(stream) {
            Ok(iter) => iter,
            Err(e) => {
                if e.is_unexpected_eof() {
                    return self.machine_st.eof_action(
                        self.machine_st.registers[2],
                        stream,
                        atom!("get_char"),
                        2,
                    );
                } else {
                    let err = self.machine_st.session_error(SessionError::from(e));
                    return Err(self.machine_st.error_form(err, stub_gen()));
                }
            }
        };

        loop {
            match iter.read_char() {
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

                    if EOFAction::Reset != stream.options().eof_action() || self.machine_st.fail {
                        break;
                    }
                }
            }
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn get_n_chars(&mut self) -> CallResult {
        let _guard = RawReadGuard::new();
        let stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices,
            atom!("get_n_chars"),
            3,
        )?;

        let num = match Number::try_from((self.deref_register(2), &self.machine_st.arena.f64_tbl)) {
            Ok(Number::Fixnum(n)) => usize::try_from(n.get_num()).unwrap(),
            Ok(Number::Integer(n)) => match (&*n).try_into() as Result<usize, _> {
                Ok(u) => u,
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
            let mut iter = self.machine_st.open_parsing_stream(stream).map_err(|e| {
                let err = self.machine_st.session_error(SessionError::from(e));
                let stub = functor_stub(atom!("get_n_chars"), 2);

                self.machine_st.error_form(err, stub)
            })?;

            for _ in 0..num {
                let result = iter.read_char();

                match result {
                    Some(Ok(c)) => {
                        string.push(c);
                    }
                    Some(Err(e)) => {
                        let stub = functor_stub(atom!("$get_n_chars"), 3);
                        let err = self.machine_st.session_error(SessionError::from(e));

                        return Err(self.machine_st.error_form(err, stub));
                    }
                    _ => {
                        break;
                    }
                }
            }
        };

        let output = self.deref_register(3);
        let cstr_cell = resource_error_call_result!(
            self.machine_st,
            self.machine_st.heap.allocate_cstr(&string)
        );

        unify!(self.machine_st, cstr_cell, output);
        Ok(())
    }

    #[inline(always)]
    pub(crate) fn get_code(&mut self) -> CallResult {
        let _guard = RawReadGuard::new();
        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices,
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

        if stream.past_end_of_stream()
            && (EOFAction::Reset != stream.options().eof_action() || self.machine_st.fail)
        {
            return Ok(());
        }

        let addr = self.deref_register(2);

        if stream.at_end_of_stream() {
            stream.set_past_end_of_stream(true);

            self.machine_st.unify_fixnum(Fixnum::build_with(-1), addr);

            return Ok(());
        }

        let stub_gen = || functor_stub(atom!("get_code"), 2);

        let addr = if addr.is_var() {
            addr
        } else {
            match Number::try_from((addr, &self.machine_st.arena.f64_tbl)) {
                Ok(Number::Integer(n)) => {
                    let n: u32 = (&*n).try_into().unwrap();
                    let n = std::char::from_u32(n);

                    if let Some(n) = n {
                        fixnum_as_cell!(Fixnum::build_with(u32::from(n)))
                    } else {
                        let err = self
                            .machine_st
                            .representation_error(RepFlag::InCharacterCode);
                        return Err(self.machine_st.error_form(err, stub_gen()));
                    }
                }
                Ok(Number::Fixnum(n)) => {
                    let nf = u32::try_from(n.get_num())
                        .ok()
                        .and_then(std::char::from_u32);

                    if nf.is_some() {
                        fixnum_as_cell!(n)
                    } else {
                        let err = self
                            .machine_st
                            .representation_error(RepFlag::InCharacterCode);
                        return Err(self.machine_st.error_form(err, stub_gen()));
                    }
                }
                _ => {
                    let err = self
                        .machine_st
                        .type_error(ValidType::Integer, self.machine_st.registers[2]);
                    return Err(self.machine_st.error_form(err, stub_gen()));
                }
            }
        };

        let mut iter = self.machine_st.open_parsing_stream(stream).map_err(|e| {
            let err = self.machine_st.session_error(SessionError::from(e));
            let stub = functor_stub(atom!("get_code"), 2);

            self.machine_st.error_form(err, stub)
        })?;

        loop {
            let result = iter.read_char();

            match result {
                Some(Ok(c)) => {
                    self.machine_st
                        .unify_fixnum(Fixnum::build_with(u32::from(c)), addr);
                    break;
                }
                _ => {
                    self.machine_st.eof_action(
                        self.machine_st.registers[2],
                        stream,
                        atom!("get_code"),
                        2,
                    )?;

                    if EOFAction::Reset != stream.options().eof_action() || self.machine_st.fail {
                        break;
                    }
                }
            }
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn first_stream(&mut self) {
        let first_stream = self.indices.iter_streams(..).find(|s| !s.is_null_stream());

        if let Some(first_stream) = first_stream {
            let stream = first_stream.into();

            let var = self.deref_register(1).as_var().unwrap();

            self.machine_st.bind(var, stream);
        } else {
            self.machine_st.fail = true;
        }
    }

    #[inline(always)]
    pub(crate) fn next_stream(&mut self) {
        let prev_stream = cell_as_stream!(self.deref_register(1));
        let next_stream = self
            .indices
            .iter_streams(prev_stream..)
            .filter(|s| !s.is_null_stream())
            .nth(1);

        if let Some(next_stream) = next_stream {
            let var = self.deref_register(2).as_var().unwrap();

            self.machine_st.bind(var, next_stream.into());
        } else {
            self.machine_st.fail = true;
        }
    }

    #[inline(always)]
    pub(crate) fn flush_output(&mut self) -> CallResult {
        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices,
            atom!("flush_output"),
            1,
        )?;

        if !stream.is_output_stream() {
            let stub = functor_stub(atom!("flush_output"), 1);
            let addr = HeapCellValue::from(stream);

            let err =
                self.machine_st
                    .permission_error(Permission::OutputStream, atom!("stream"), addr);

            return Err(self.machine_st.error_form(err, stub));
        }

        stream.flush().unwrap();
        Ok(())
    }

    #[cfg(feature = "repl")]
    #[inline(always)]
    pub(crate) fn get_single_char(&mut self) -> CallResult {
        let key = get_key();

        if key.code == KeyCode::Char('c') && key.modifiers == KeyModifiers::CONTROL {
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
        let a1 = self.deref_register(1);
        self.machine_st.unify_char(c, a1);

        Ok(())
    }

    #[cfg(not(feature = "repl"))]
    #[inline(always)]
    pub(crate) fn get_single_char(&mut self) -> CallResult {
        let mut buffer = [0; 1];
        // is there a better way?
        if std::io::stdin().read(&mut buffer).is_err() {
            let stub = functor_stub(atom!("get_single_char"), 1);
            let err = self.machine_st.interrupt_error();
            let err = self.machine_st.error_form(err, stub);

            return Err(err);
        }
        let c = buffer[0] as char;
        let a1 = self.deref_register(1);
        self.machine_st.unify_char(c, a1);

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn head_is_dynamic(&mut self) {
        let module_name = cell_as_atom!(self.deref_register(1));

        match self
            .machine_st
            .name_and_arity_from_heap(self.machine_st.registers[2])
        {
            Some((name, arity)) => {
                self.machine_st.fail = !self
                    .indices
                    .is_dynamic_predicate(module_name, (name, arity));
            }
            None => {
                self.machine_st.fail = true;
            }
        }
    }

    #[inline(always)]
    pub(crate) fn close(&mut self) -> CallResult {
        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices,
            atom!("close"),
            2,
        )?;

        if !stream.is_input_stream() {
            stream.flush().unwrap(); // 8.11.6.1b)
        }

        if stream == self.user_input || stream == self.user_output || stream.is_stderr() {
            // stdin, stdout and stderr shouldn't be removed from the store, so return now
            return Ok(());
        }

        self.indices.remove_stream(stream);

        stream.close().map_err(|_| {
            let stub = functor_stub(atom!("close"), 1);
            let addr = stream.into();
            let err = self
                .machine_st
                .existence_error(ExistenceError::Stream(addr));

            self.machine_st.error_form(err, stub)
        })
    }

    #[inline(always)]
    pub(crate) fn copy_to_lifted_heap(&mut self) {
        let lh_offset =
            unsafe { self.deref_register(1).to_fixnum_or_cut_point_unchecked() }.get_num() as usize;
        let copy_target = self.machine_st.registers[2];
        let FindallCopyInfo {
            offset: old_threshold,
            pstr_threshold,
        } = step_or_resource_error!(
            self.machine_st,
            self.machine_st
                .copy_findall_solution(lh_offset, copy_target)
        );

        let new_threshold = self.machine_st.lifted_heap.cell_len() - lh_offset;

        self.machine_st.lifted_heap[old_threshold] = heap_loc_as_cell!(new_threshold);

        for idx in old_threshold + 1..pstr_threshold {
            self.machine_st.lifted_heap[idx] -= self.machine_st.heap.cell_len() + lh_offset;
        }

        self.machine_st.lifted_heap[old_threshold + 1] = fixnum_as_cell!(
            /* FIXME this is not safe */
            unsafe { Fixnum::build_with_unchecked(pstr_threshold as i64) }
        );
        self.machine_st.lifted_heap[old_threshold + 2] =
            fixnum_as_cell!(/* FIXME this is not safe */ unsafe {
                Fixnum::build_with_unchecked(self.machine_st.lifted_heap.cell_len() as i64)
            });

        let mut pstr_threshold = heap_index!(pstr_threshold);

        while pstr_threshold < heap_index!(self.machine_st.lifted_heap.cell_len()) {
            let HeapStringScan { tail_idx, .. } = self
                .machine_st
                .lifted_heap
                .scan_slice_to_str(pstr_threshold);

            self.machine_st.lifted_heap[tail_idx] -= self.machine_st.heap.cell_len() + lh_offset;
            pstr_threshold = heap_index!(tail_idx + 1);
        }
    }

    #[inline(always)]
    pub(crate) fn lookup_db_ref(&mut self) {
        let module_name = self.deref_register(1);
        let name = cell_as_atom!(self.deref_register(2));
        let arity =
            unsafe { self.deref_register(3).to_fixnum_or_cut_point_unchecked() }.get_num() as usize;

        let module_name = read_heap_cell!(module_name,
            (HeapCellValueTag::Atom, (module_name, _arity)) => {
                module_name
            }
            (HeapCellValueTag::AttrVar | HeapCellValueTag::Var) => {
                atom!("user")
            }
            _ => {
                unreachable!()
            }
        );

        if self.indices.builtin_property((name, arity)) {
            self.machine_st.fail = true;
            return;
        }

        self.machine_st.fail = self
            .indices
            .get_predicate_code_index(name, arity, module_name)
            .is_none();
    }

    #[inline(always)]
    pub(crate) fn get_db_refs(&mut self) {
        let name_match: fn(Atom, Atom) -> bool;
        let arity_match: fn(usize, usize) -> bool;

        let module_name = read_heap_cell!(self.deref_register(1),
            (HeapCellValueTag::Atom, (module_name, _arity)) => {
                module_name
            }
            (HeapCellValueTag::AttrVar | HeapCellValueTag::Var | HeapCellValueTag::StackVar) => {
                atom!("user")
            }
            _ => {
                unreachable!()
            }
        );

        let atom = self.deref_register(2);

        let pred_atom = if atom.is_var() {
            name_match = |_, _| true;
            atom!("")
        } else {
            name_match = |atom_1, atom_2| atom_1 == atom_2;
            cell_as_atom!(atom)
        };

        let arity = self.deref_register(3);

        let pred_arity = if arity.is_var() {
            arity_match = |_, _| true;
            0
        } else {
            arity_match = |arity_1, arity_2| arity_1 == arity_2;

            let arity = match Number::try_from((arity, &self.machine_st.arena.f64_tbl)) {
                Ok(Number::Fixnum(n)) => Some(n.get_num() as usize),
                Ok(Number::Integer(n)) => {
                    let value: usize = (&*n).try_into().unwrap();
                    Some(value)
                }
                _ => None,
            };

            if let Some(arity) = arity {
                arity
            } else {
                self.machine_st.fail = true;
                return;
            }
        };

        let h = self.machine_st.heap.cell_len();
        let mut num_functors = 0;

        let code_dir = if module_name == atom!("user") {
            &self.indices.code_dir
        } else {
            match self
                .indices
                .modules
                .get(&module_name)
                .map(|module| &module.code_dir)
            {
                Some(code_dir) => code_dir,
                None => {
                    self.machine_st.fail = true;
                    return;
                }
            }
        };

        for (name, arity) in code_dir.keys().cloned() {
            if self.indices.builtin_property((name, arity)) {
                continue;
            }

            if name_match(pred_atom, name) && arity_match(pred_arity, arity) {
                let functor = functor!(atom!("/"), [atom_as_cell(name), fixnum(arity)]); // self.machine_st.heap.extend(

                let mut functor_writer = Heap::functor_writer(functor);

                step_or_resource_error!(self.machine_st, functor_writer(&mut self.machine_st.heap));

                num_functors += 1;
            }
        }

        let functor_list_cell = step_or_resource_error!(
            self.machine_st,
            sized_iter_to_heap_list(
                &mut self.machine_st.heap,
                num_functors,
                (0..num_functors).map(|i| str_loc_as_cell!(h + 3 * i))
            )
        );

        unify!(
            self.machine_st,
            functor_list_cell,
            self.machine_st.registers[4]
        );
    }

    #[inline(always)]
    pub(crate) fn get_next_op_db_ref(&mut self) {
        let prec = self.deref_register(1);
        let h = self.machine_st.heap.cell_len();

        fn write_op_functors_to_heap(
            heap: &mut Heap,
            op_descs: impl Iterator<Item = (Atom, OpDesc)>,
        ) -> Result<usize, usize> {
            let mut num_functors = 0;

            for (name, op_desc) in op_descs {
                let prec = op_desc.get_prec();

                if prec == 0 {
                    // 8.14.4, note 2
                    continue;
                }

                let spec_atom = op_desc.get_spec().get_spec();

                let functor = functor!(
                    atom!("op"),
                    [fixnum(prec), atom_as_cell(spec_atom), atom_as_cell(name)]
                );

                let mut functor_writer = Heap::functor_writer(functor);

                functor_writer(heap)?;

                num_functors += 1;
            }

            Ok(num_functors)
        }

        if prec.is_var() {
            let spec = self.deref_register(2);
            let orig_op = self.deref_register(3);

            let spec_num = if spec.get_tag() == HeapCellValueTag::Atom {
                OpDeclSpec::try_from(cell_as_atom!(spec)).ok()
            } else {
                None
            };

            let num_functors = if !orig_op.is_var() {
                let orig_op = read_heap_cell!(orig_op,
                    (HeapCellValueTag::Atom, (name, _arity)) => {
                        name
                    }
                    (HeapCellValueTag::Str, s) => {
                        cell_as_atom!(self.machine_st.heap[s])
                    }
                    /*
                    (HeapCellValueTag::Char, c) => {
                        AtomTable::build_with(&self.machine_st.atom_tbl, &c.to_string())
                    }
                    */
                    _ => {
                        unreachable!()
                    }
                );

                let op_descs = [
                    self.indices.op_dir.get(&(orig_op, Fixity::In)),
                    self.indices.op_dir.get(&(orig_op, Fixity::Pre)),
                    self.indices.op_dir.get(&(orig_op, Fixity::Post)),
                ];

                let number_of_keys = op_descs[0].is_some() as usize
                    + op_descs[1].is_some() as usize
                    + op_descs[2].is_some() as usize;

                let op_descs = op_descs
                    .into_iter()
                    .filter_map(|op_desc| op_desc.map(|op_desc| (orig_op, *op_desc)));

                if number_of_keys == 0 {
                    self.machine_st.fail = true;
                } else {
                    let num_functors = step_or_resource_error!(
                        self.machine_st,
                        write_op_functors_to_heap(&mut self.machine_st.heap, op_descs,)
                    );

                    let functor_list_cell = step_or_resource_error!(
                        self.machine_st,
                        sized_iter_to_heap_list(
                            &mut self.machine_st.heap,
                            num_functors,
                            (0..num_functors).map(|i| str_loc_as_cell!(h + 4 * i))
                        )
                    );

                    unify!(
                        self.machine_st,
                        functor_list_cell,
                        self.machine_st.registers[4]
                    );
                }

                return;
            } else {
                let op_descs = self.indices.op_dir.iter().filter_map(|(key, op_desc)| {
                    let (other_prec, other_spec) = (op_desc.get_prec(), op_desc.get_spec());
                    let name = key.0;

                    if other_prec == 0 {
                        // 8.14.4, note 2
                        return None;
                    }

                    if (!orig_op.is_var() && atom_as_cell!(name) != orig_op)
                        || (!spec.is_var() && Some(other_spec) != spec_num)
                    {
                        return None;
                    }

                    Some((key.0, *op_desc))
                });

                step_or_resource_error!(
                    self.machine_st,
                    write_op_functors_to_heap(&mut self.machine_st.heap, op_descs,)
                )
            };

            let functor_list_cell = step_or_resource_error!(
                self.machine_st,
                sized_iter_to_heap_list(
                    &mut self.machine_st.heap,
                    num_functors,
                    (0..num_functors).map(|i| str_loc_as_cell!(h + 4 * i)),
                )
            );

            unify!(
                self.machine_st,
                functor_list_cell,
                self.machine_st.registers[4]
            );
        } else {
            let spec = cell_as_atom!(self.deref_register(2));
            let op_atom = cell_as_atom!(self.deref_register(3));

            let fixity = match spec {
                atom!("xfy") | atom!("yfx") | atom!("xfx") => Fixity::In,
                atom!("xf") | atom!("yf") => Fixity::Post,
                atom!("fx") | atom!("fy") => Fixity::Pre,
                _ => {
                    self.machine_st.fail = true;
                    return;
                }
            };

            match self.indices.op_dir.get(&(op_atom, fixity)).cloned() {
                Some(op_desc) => {
                    let num_functors = step_or_resource_error!(
                        self.machine_st,
                        write_op_functors_to_heap(
                            &mut self.machine_st.heap,
                            std::iter::once((op_atom, op_desc))
                        )
                    );

                    let functor_list = step_or_resource_error!(
                        self.machine_st,
                        sized_iter_to_heap_list(
                            &mut self.machine_st.heap,
                            num_functors,
                            (0..num_functors).map(|i| str_loc_as_cell!(h + 4 * i)),
                        )
                    );

                    unify!(self.machine_st, functor_list, self.machine_st.registers[4]);
                }
                _ => {
                    self.machine_st.fail = true;
                }
            }
        }
    }

    #[inline(always)]
    pub(crate) fn random_integer(&mut self) {
        let a1 = self.deref_register(1);
        let a2 = self.deref_register(2);
        let value = match (
            Number::try_from((a1, &self.machine_st.arena.f64_tbl)),
            Number::try_from((a2, &self.machine_st.arena.f64_tbl)),
        ) {
            (Ok(Number::Fixnum(lower)), Ok(Number::Fixnum(upper))) => {
                let (lower, upper) = (lower.get_num(), upper.get_num());
                if lower >= upper {
                    self.machine_st.fail = true;
                    return;
                }
                let value = self.rng.gen_range(lower..upper);
                // Safety:
                // - lower and uper bounds are Fixnum values
                // - value is inbetween lower and upper
                // - fixnums value range has no gaps
                // so value is also a valid Fixnum value
                Number::Fixnum(unsafe { Fixnum::build_with_unchecked(value) })
            }
            (Ok(Number::Fixnum(lower)), Ok(Number::Integer(upper))) => {
                let lower = Integer::from(lower);
                if lower >= *upper {
                    self.machine_st.fail = true;
                    return;
                }
                let value = self.rng.gen_range(lower..(*upper).clone());
                Number::arena_from(value, &mut self.machine_st.arena)
            }
            (Ok(Number::Integer(lower)), Ok(Number::Fixnum(upper))) => {
                let upper = Integer::from(upper);
                if *lower >= upper {
                    self.machine_st.fail = true;
                    return;
                }
                let value = self.rng.gen_range((*lower).clone()..upper);
                Number::arena_from(value, &mut self.machine_st.arena)
            }
            (Ok(Number::Integer(lower)), Ok(Number::Integer(upper))) => {
                if *lower >= *upper {
                    self.machine_st.fail = true;
                    return;
                }
                let value = self.rng.gen_range((*lower).clone()..(*upper).clone());
                Number::arena_from(value, &mut self.machine_st.arena)
            }
            _ => {
                self.machine_st.fail = true;
                return;
            }
        };
        let a3 = self.deref_register(3);
        match value {
            Number::Fixnum(n) => {
                self.machine_st.unify_fixnum(n, a3);
            }
            Number::Integer(n) => {
                self.machine_st.unify_big_int(n, a3);
            }
            _ => unreachable!(),
        }
    }

    #[inline(always)]
    pub(crate) fn maybe(&mut self) {
        self.machine_st.fail = self.rng.gen();
    }

    #[cfg(not(target_arch = "wasm32"))]
    #[inline(always)]
    pub(crate) fn cpu_now(&mut self) {
        let secs = ProcessTime::now().as_duration().as_secs_f64();
        let secs = float_alloc!(secs, self.machine_st.arena);

        self.machine_st
            .unify_f64(secs, self.machine_st.registers[1]);
    }

    #[cfg(target_arch = "wasm32")]
    #[inline(always)]
    pub(crate) fn cpu_now(&mut self) {
        let millisecs = web_sys::window()
            .expect("window global object should be available")
            .performance()
            .expect("performance property in window should be available")
            .now();
        let secs = float_alloc!(millisecs / 1000.0, self.machine_st.arena);

        self.machine_st.unify_f64(secs, self.deref_register(1));
    }

    #[inline(always)]
    pub(crate) fn det_length_rundown(&mut self) -> CallResult {
        let stub_gen = || functor_stub(atom!("length"), 2);
        let len = self.deref_register(2);

        let n = match Number::try_from((len, &self.machine_st.arena.f64_tbl)) {
            Ok(Number::Fixnum(n)) => n.get_num() as usize,
            Ok(Number::Integer(n)) => match (&*n).try_into() as Result<usize, _> {
                Ok(n) => n,
                Err(_) => {
                    let err = MachineState::resource_error(ResourceError::FiniteMemory(len));
                    return Err(self.machine_st.error_form(err, stub_gen()));
                }
            },
            _ => {
                unreachable!()
            }
        };

        let h = self.machine_st.heap.cell_len();

        let list_cell = resource_error_call_result!(
            self.machine_st,
            sized_iter_to_heap_list(
                &mut self.machine_st.heap,
                n,
                (0..n).map(|i| heap_loc_as_cell!(h + 2 * i + 1)),
            )
        );

        unify!(self.machine_st, self.deref_register(1), list_cell);
        Ok(())
    }

    #[cfg(feature = "http")]
    #[inline(always)]
    pub(crate) fn http_open(&mut self) -> CallResult {
        let address_sink = self.deref_register(1);
        let method = read_heap_cell!(self.deref_register(3),
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
        let address_status = self.deref_register(4);
        let address_data = self.deref_register(5);
        let mut bytes: Vec<u8> = Vec::new();
        if let Some(string) = self.machine_st.value_to_str_like(address_data) {
            bytes = string.as_str().bytes().collect();
        }
        let stub_gen = || functor_stub(atom!("http_open"), 3);

        let headers = match self
            .machine_st
            .try_from_list(self.machine_st.registers[7], stub_gen)
        {
            Ok(addrs) => {
                let mut header_map = HeaderMap::new();
                for heap_cell in addrs {
                    read_heap_cell!(heap_cell,
                        (HeapCellValueTag::Str, s) => {
                            let name = cell_as_atom_cell!(self.machine_st.heap[s]).get_name();
                            let value = self.machine_st.value_to_str_like(self.machine_st.heap[s + 1]).unwrap();
                            header_map.insert(HeaderName::from_str(&name.as_str()).unwrap(), HeaderValue::from_str(&value.as_str()).unwrap());
                        }
                        _ => {
                            unreachable!()
                        }
                    )
                }
                header_map
            }
            Err(e) => return Err(e),
        };
        if let Some(address_sink) = self.machine_st.value_to_str_like(address_sink) {
            let address_string = address_sink.as_str(); //to_string();
            let address: Url = address_string.parse().unwrap();

            let client = reqwest::Client::builder().build().unwrap();

            // request
            let mut req = client.request(method, address).headers(headers);

            if !bytes.is_empty() {
                req = req.body(bytes);
            }

            // do it!
            task::block_in_place(move || {
                match Handle::current().block_on(req.send()) {
                    Ok(resp) => {
                        // status code
                        let status = resp.status().as_u16();
                        self.machine_st
                            .unify_fixnum(Fixnum::build_with(status), address_status);
                        // headers
                        let mut headers: Vec<HeapCellValue> = vec![];

                        for (header_name, header_value) in resp.headers().iter() {
                            let string_cell = resource_error_call_result!(
                                self.machine_st,
                                self.machine_st
                                    .heap
                                    .allocate_cstr(header_value.to_str().unwrap())
                            );

                            let header_term = functor!(
                                AtomTable::build_with(
                                    &self.machine_st.atom_tbl,
                                    header_name.as_str()
                                ),
                                [cell(string_cell)]
                            );

                            let mut functor_writer = Heap::functor_writer(header_term);

                            let functor_cell = resource_error_call_result!(
                                self.machine_st,
                                functor_writer(&mut self.machine_st.heap)
                            );

                            headers.push(functor_cell);
                        }

                        let headers_list_cell = resource_error_call_result!(
                            self.machine_st,
                            sized_iter_to_heap_list(
                                &mut self.machine_st.heap,
                                headers.len(),
                                headers.into_iter(),
                            )
                        );

                        unify!(
                            self.machine_st,
                            headers_list_cell,
                            self.machine_st.registers[6]
                        );

                        // body
                        let reader = futures::executor::block_on(resp.bytes()).unwrap().reader();

                        let mut stream = Stream::from_http_stream(
                            AtomTable::build_with(&self.machine_st.atom_tbl, &address_string),
                            reader,
                            &mut self.machine_st.arena,
                        );
                        *stream.options_mut() = StreamOptions::default();

                        self.indices
                            .add_stream(stream, atom!("http_open"), 3)
                            .map_err(|stub_gen| stub_gen(&mut self.machine_st))
                            .unwrap();

                        let stream_addr = self.deref_register(2);
                        self.machine_st
                            .bind(stream_addr.as_var().unwrap(), stream.into());
                    }
                    Err(_) => {
                        self.machine_st.fail = true;
                    }
                }

                Ok::<(), _>(())
            })?;
        } else {
            let err = self
                .machine_st
                .domain_error(DomainErrorType::SourceSink, address_sink);
            let stub = functor_stub(atom!("http_open"), 3);

            return Err(self.machine_st.error_form(err, stub));
        }

        Ok(())
    }

    #[cfg(feature = "http")]
    #[inline(always)]
    pub(crate) fn http_listen(&mut self) -> CallResult {
        let address_sink = self.deref_register(1);
        let tls_key = self.deref_register(3);
        let tls_cert = self.deref_register(4);
        let content_length_limit = self.deref_register(5);
        const CONTENT_LENGTH_LIMIT_DEFAULT: u64 = 32768;
        let content_length_limit =
            match Number::try_from((content_length_limit, &self.machine_st.arena.f64_tbl)) {
                Ok(Number::Fixnum(n)) => {
                    if n.get_num() >= 0 {
                        n.get_num() as u64
                    } else {
                        CONTENT_LENGTH_LIMIT_DEFAULT
                    }
                }
                Ok(Number::Integer(n)) => {
                    let n: Result<u64, _> = (&*n).try_into();
                    match n {
                        Ok(u) => u,
                        Err(_) => CONTENT_LENGTH_LIMIT_DEFAULT,
                    }
                }
                _ => CONTENT_LENGTH_LIMIT_DEFAULT,
            };

        let ssl_server: Option<(String, String)> = {
            match self.machine_st.value_to_str_like(tls_key) {
                Some(key) => match self.machine_st.value_to_str_like(tls_cert) {
                    Some(cert) => {
                        let key_str = key.as_str();
                        let cert_str = cert.as_str();

                        if key_str.is_empty() || cert_str.is_empty() {
                            None
                        } else {
                            Some((key_str.to_string(), cert_str.to_string()))
                        }
                    }
                    None => None,
                },
                None => None,
            }
        };

        if let Some(address_str) = self.machine_st.value_to_str_like(address_sink) {
            let address_string = address_str.as_str();
            let addr: SocketAddr = match address_string
                .to_socket_addrs()
                .ok()
                .and_then(|mut s| s.next())
            {
                Some(addr) => addr,
                _ => {
                    self.machine_st.fail = true;
                    return Ok(());
                }
            };

            let (tx, rx) = std::sync::mpsc::sync_channel(1024);

            let runtime = tokio::runtime::Handle::current();
            let _guard = runtime.enter();

            let serve = warp::body::bytes()
                .and(warp::header::optional::<u64>(
                    warp::http::header::CONTENT_LENGTH.as_str(),
                ))
                .and(warp::method())
                .and(warp::header::headers_cloned())
                .and(warp::path::full())
                .and(warp::query::raw().or_else(|_| {
                    future::ready(Ok::<(String,), warp::Rejection>(("".to_string(),)))
                }))
                .map(
                    move |body: bytes::Bytes,
                          content_length,
                          method,
                          headers: warp::http::HeaderMap,
                          path: warp::filters::path::FullPath,
                          query| {
                        if let Some(content_length) = content_length {
                            if content_length > content_length_limit {
                                return warp::http::Response::builder()
                                    .status(413)
                                    .body(warp::hyper::Body::empty())
                                    .unwrap();
                            }
                        }

                        let http_request_data = HttpRequestData {
                            method,
                            headers,
                            path: path.as_str().to_string(),
                            query,
                            body: body.reader(),
                        };
                        let response =
                            Arc::new((Mutex::new(false), Mutex::new(None), Condvar::new()));
                        let http_request = HttpRequest {
                            request_data: http_request_data,
                            response: Arc::clone(&response),
                        };
                        // we send the request to http_accept
                        tx.send(http_request).unwrap();

                        // we wait for the Response info from Prolog
                        {
                            let (ready, _response, cvar) = &*response;
                            let mut ready = ready.lock().unwrap();
                            while !*ready {
                                ready = cvar.wait(ready).unwrap();
                            }
                        }
                        {
                            let (_, response, _) = &*response;
                            let response = response.lock().unwrap().take();
                            response.expect("Data race error in HTTP server")
                        }
                    },
                );

            runtime.spawn(async move {
                match ssl_server {
                    Some((key, cert)) => {
                        warp::serve(serve).tls().key(key).cert(cert).run(addr).await
                    }
                    None => warp::serve(serve).run(addr).await,
                }
            });

            let http_listener = HttpListener { incoming: rx };
            let http_listener: TypedArenaPtr<HttpListener> =
                arena_alloc!(http_listener, &mut self.machine_st.arena);

            let addr = self.deref_register(2);
            self.machine_st.bind(
                addr.as_var().unwrap(),
                typed_arena_ptr_as_cell!(http_listener),
            );
        }
        Ok(())
    }

    #[cfg(feature = "http")]
    #[inline(always)]
    pub(crate) fn http_accept(&mut self) -> CallResult {
        let culprit = self.deref_register(1);
        let method = self.deref_register(2);
        let path = self.deref_register(3);
        let query = self.deref_register(5);
        let stream_addr = self.deref_register(6);
        let handle_addr = self.deref_register(7);
        read_heap_cell!(culprit,
        (HeapCellValueTag::Cons, cons_ptr) => {
        match_untyped_arena_ptr!(cons_ptr,
            (ArenaHeaderTag::HttpListener, http_listener) => {
            loop {
                match http_listener.incoming.recv_timeout(std::time::Duration::from_millis(200)) {
                    Ok(request) => {
                        let method_atom = match request.request_data.method {
                            Method::GET => atom!("get"),
                            Method::POST => atom!("post"),
                            Method::PUT => atom!("put"),
                            Method::DELETE => atom!("delete"),
                            Method::PATCH => atom!("patch"),
                            Method::HEAD => atom!("head"),
                            Method::OPTIONS => atom!("options"),
                            Method::TRACE => atom!("trace"),
                            Method::CONNECT => atom!("connect"),
                            _ => atom!("unsupported_extension"),
                        };

                        let path_atom = AtomTable::build_with(&self.machine_st.atom_tbl, &request.request_data.path);
                        let path_cell = resource_error_call_result!(
                            self.machine_st,
                            self.machine_st.heap.allocate_cstr(&request.request_data.path)
                        );

                        let mut headers = vec![];

                        for (header_name, header_value) in request.request_data.headers {
                            let header_value = resource_error_call_result!(
                                self.machine_st,
                                self.machine_st.heap.allocate_cstr(header_value.to_str().unwrap())
                            );

                            let header_term = functor!(
                                AtomTable::build_with(&self.machine_st.atom_tbl, header_name.unwrap().as_str()),
                                [cell(header_value)]
                            );

                            let mut functor_writer = Heap::functor_writer(header_term);

                            let functor_cell = resource_error_call_result!(
                                self.machine_st,
                                functor_writer(&mut self.machine_st.heap)
                            );

                            headers.push(functor_cell);
                        }

                        let headers_list_cell = resource_error_call_result!(
                            self.machine_st,
                            sized_iter_to_heap_list(
                                &mut self.machine_st.heap,
                                headers.len(),
                                headers.into_iter(),
                            )
                        );

                        let query_str  = request.request_data.query;
                        let query_cell = resource_error_call_result!(
                            self.machine_st,
                            self.machine_st.heap.allocate_cstr(&query_str)
                        );

                        let mut stream = Stream::from_http_stream(
                            path_atom,
                            request.request_data.body,
                            &mut self.machine_st.arena
                        );
                        *stream.options_mut() = StreamOptions::default();
                        stream.options_mut().set_stream_type(StreamType::Binary);

                        self.indices.add_stream(stream, atom!("http_accept"), 7)
                            .map_err(|stub_gen| stub_gen(&mut self.machine_st))?;

                        let stream = stream_as_cell!(stream);

                        let handle = arena_alloc!(request.response, &mut self.machine_st.arena)
                            as TypedArenaPtr<HttpResponse>;

                        self.machine_st.bind(method.as_var().unwrap(), atom_as_cell!(method_atom));
                        self.machine_st.bind(path.as_var().unwrap(), path_cell);
                        unify!(self.machine_st, headers_list_cell, self.machine_st.registers[4]);
                        self.machine_st.bind(query.as_var().unwrap(), query_cell);
                        self.machine_st.bind(stream_addr.as_var().unwrap(), stream);
                        self.machine_st.bind(handle_addr.as_var().unwrap(), typed_arena_ptr_as_cell!(handle));

                        break
                    }
                    Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
                        let interrupted = machine::INTERRUPT.load(std::sync::atomic::Ordering::Relaxed);

                        match machine::INTERRUPT.compare_exchange(
                            interrupted,
                            false,
                            std::sync::atomic::Ordering::Relaxed,
                            std::sync::atomic::Ordering::Relaxed,
                        ) {
                            Ok(interruption) => {
                                if interruption {
                                    self.machine_st.throw_interrupt_exception();
                                    self.machine_st.backtrack();
                                    // We have extracted controll over the Tokio runtime to the calling context for enabling library use case
                                    // (see https://github.com/mthom/scryer-prolog/pull/1880)
                                    // So we only have access to a runtime handle in here and can't shut it down.
                                    // Since I'm not aware of the consequences of deactivating this new code which came in while PR 1880
                                    // was not merged, I'm only deactivating it for now.
                                    //let old_runtime = std::mem::replace(&mut self.runtime, tokio::runtime::Runtime::new().unwrap());
                                    //old_runtime.shutdown_background();
                                    break
                                }
                            }
                            Err(_) => unreachable!(),
                        }
                    }
                  Err(_) => {
                      self.machine_st.fail = true;
                  }
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

    #[cfg(feature = "http")]
    #[inline(always)]
    pub(crate) fn http_answer(&mut self) -> CallResult {
        let culprit = self.deref_register(1);
        let status_code = self.deref_register(2);
        let status_code: u16 = match Number::try_from((status_code, &self.machine_st.arena.f64_tbl))
        {
            Ok(Number::Fixnum(n)) => n.get_num() as u16,
            Ok(Number::Integer(n)) => {
                let n: Result<u16, _> = (&*n).try_into();

                if let Ok(value) = n {
                    value
                } else {
                    self.machine_st.fail = true;
                    return Ok(());
                }
            }
            _ => unreachable!(),
        };
        let stub_gen = || functor_stub(atom!("http_listen"), 2);
        let headers = match self
            .machine_st
            .try_from_list(self.machine_st.registers[3], stub_gen)
        {
            Ok(addrs) => {
                let mut header_map = HeaderMap::new();
                for heap_cell in addrs {
                    read_heap_cell!(heap_cell,
                        (HeapCellValueTag::Str, s) => {
                            let name = cell_as_atom_cell!(self.machine_st.heap[s]).get_name();
                            let value = self.machine_st.value_to_str_like(self.machine_st.heap[s + 1]).unwrap();
                            header_map.insert(HeaderName::from_str(&name.as_str()).unwrap(), HeaderValue::from_str(&value.as_str()).unwrap());
                        }
                        _ => {
                            unreachable!()
                        }
                    )
                }
                header_map
            }
            Err(e) => return Err(e),
        };
        let stream_addr = self.deref_register(4);

        read_heap_cell!(culprit,
            (HeapCellValueTag::Cons, cons_ptr) => {
                match_untyped_arena_ptr!(cons_ptr,
                    (ArenaHeaderTag::HttpResponse, http_response) => {
                        let mut stream = Stream::from_http_sender(
                            http_response,
                            status_code,
                            headers,
                            &mut self.machine_st.arena
                        );

                        *stream.options_mut() = StreamOptions::default();
                        stream.options_mut().set_stream_type(StreamType::Binary);

                        self.indices.add_stream(stream, atom!("http_answer"), 4)
                            .map_err(|stub_gen| stub_gen(&mut self.machine_st))?;
                        self.machine_st.bind(stream_addr.as_var().unwrap(), stream.into());
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
    pub(crate) fn load_foreign_lib(&mut self) -> CallResult {
        fn stub_gen() -> MachineStub {
            functor_stub(atom!("$load_foreign_lib"), 2)
        }

        #[cfg(feature = "ffi")]
        {
            let library_name = self.deref_register(1);
            let args_reg = self.deref_register(2);
            if let Some(library_name) = self.machine_st.value_to_str_like(library_name) {
                match self.machine_st.try_from_list(args_reg, stub_gen) {
                    Ok(addrs) => {
                        let mut functions = Vec::new();
                        for heap_cell in addrs {
                            read_heap_cell!(heap_cell,
                                (HeapCellValueTag::Str, s) => {
                                    let name = cell_as_atom_cell!(self.machine_st.heap[s]).get_name();
                                let args: Vec<Atom> = match self.machine_st.try_from_list(self.machine_st.heap[s + 1], stub_gen) {
                                    Ok(addrs) => {
                                    let mut args = Vec::new();
                                    for heap_cell in addrs {
                                        args.push(cell_as_atom_cell!(heap_cell).get_name());
                                    }
                                    args
                                    }
                                    Err(e) => return Err(e)
                                };
                                let return_value = cell_as_atom_cell!(self.machine_st.heap[s + 2]);
                                functions.push(FunctionDefinition {
                                    name,
                                    args,
                                    return_value: return_value.get_name(),
                                });
                                }
                                _ => {
                                    let err = self.machine_st.unreachable_error();
                                    return Err(self.machine_st.error_form(err, stub_gen()))
                                }
                            )
                        }
                        if self
                            .foreign_function_table
                            .load_library(&library_name.as_str(), &functions)
                            .is_err()
                        {
                            self.machine_st.fail = true;
                        }

                        Ok(())
                    }
                    Err(e) => Err(e),
                }
            } else {
                let err = self
                    .machine_st
                    .type_error(ValidType::InCharacter, library_name);
                Err(self.machine_st.error_form(err, stub_gen()))
            }
        }

        #[cfg(not(feature = "ffi"))]
        {
            let err = self.machine_st.missing_feature_error(atom!("ffi"));
            Err(self.machine_st.error_form(err, stub_gen()))
        }
    }

    #[cfg(feature = "ffi")]
    fn map_ffi_arg(
        &mut self,
        source: HeapCellValue,
        stub_gen: impl Copy + Fn() -> MachineStub,
    ) -> CallResult<Value> {
        let source = self.machine_st.store(self.machine_st.deref(source));
        if let Ok(number) = Number::try_from((source, &self.machine_st.arena.f64_tbl)) {
            Ok(Value::Number(number))
        } else if let Some(string) = self.machine_st.value_to_str_like(source) {
            Ok(Value::CString(CString::new(&*string.as_str()).unwrap()))
        } else if let Ok(args) = self.machine_st.try_from_list(source, stub_gen) {
            // structs are lists represented as lists
            // the head is a string with the struct type name
            // the tail are the struct field values

            let mut iter = args.into_iter();

            if let Some(head) = iter.next() {
                let head = self.machine_st.store(self.machine_st.deref(head));
                if let Some(struct_name) = head.to_atom() {
                    Ok(Value::Struct(
                        struct_name,
                        iter.map(|x| self.map_ffi_arg(x, stub_gen))
                            .collect::<Result<_, _>>()?,
                    ))
                } else if head.is_var() {
                    let err = self.machine_st.instantiation_error();

                    let src = stub_gen();

                    let culprit = functor!(atom!("-"), [atom_as_cell((atom!("var"))), cell(head)]);

                    let src = functor!(atom!("."), [functor(culprit), list([functor(src)])]);

                    Err(self.machine_st.error_form(err, src))
                } else {
                    // first element of a struct needs to be the type
                    let err = self.machine_st.type_error(ValidType::Atom, head);
                    Err(self.machine_st.error_form(err, stub_gen()))
                }
            } else {
                // empty list is an invalid struct repr
                let err = self
                    .machine_st
                    .domain_error(DomainErrorType::FfiStruct, source);
                Err(self.machine_st.error_form(err, stub_gen()))
            }
        } else if self.machine_st.deref(source).is_var() {
            let err = self.machine_st.instantiation_error();

            let src = stub_gen();

            let culprit = functor!(atom!("-"), [atom_as_cell((atom!("var"))), cell(source)]);

            let src = functor!(atom!("."), [functor(culprit), list([functor(src)])]);

            Err(self.machine_st.error_form(err, src))
        } else {
            let err = self
                .machine_st
                .domain_error(DomainErrorType::FfiArgument, source);
            Err(self.machine_st.error_form(err, stub_gen()))
        }
    }

    #[inline(always)]
    pub(crate) fn foreign_call(&mut self) -> CallResult {
        fn stub_gen() -> Vec<FunctorElement> {
            functor_stub(atom!("$foreign_call"), 3)
        }

        #[cfg(feature = "ffi")]
        {
            let function_name_arg = self.machine_st.store(self.deref_register(1));
            let args_reg = self.deref_register(2);
            let return_value = self.deref_register(3);
            if let Some(function_name) = function_name_arg.to_atom() {
                match self.machine_st.try_from_list(args_reg, stub_gen) {
                    Ok(args) => {
                        let args = args
                            .into_iter()
                            .map(|x| self.map_ffi_arg(x, stub_gen))
                            .collect::<Result<Vec<_>, _>>()?;

                        match self.foreign_function_table.exec(
                            function_name,
                            args,
                            &mut self.machine_st.arena,
                        ) {
                            Ok(result) => self.unify_ffi_result(return_value, result),
                            Err(e) => {
                                let err = self.machine_st.ffi_error(e);
                                Err(self.machine_st.error_form(err, stub_gen()))
                            }
                        }
                    }
                    Err(e) => Err(e),
                }
            } else {
                let err = self
                    .machine_st
                    .type_error(ValidType::Atom, function_name_arg);
                Err(self.machine_st.error_form(err, stub_gen()))
            }
        }

        #[cfg(not(feature = "ffi"))]
        {
            let err = self.machine_st.missing_feature_error(atom!("ffi"));
            Err(self.machine_st.error_form(err, stub_gen()))
        }
    }

    #[cfg(feature = "ffi")]
    fn unify_ffi_result(&mut self, return_value: HeapCellValue, result: Value) -> CallResult {
        match result {
            Value::Number(n) => match n {
                Number::Float(OrderedFloat(n)) => {
                    let n = float_alloc!(n, self.machine_st.arena);
                    self.machine_st.unify_f64(n, return_value)
                }
                Number::Integer(typed_arena_ptr) => {
                    self.machine_st.unify_big_int(typed_arena_ptr, return_value)
                }
                Number::Rational(typed_arena_ptr) => {
                    self.machine_st
                        .unify_rational(typed_arena_ptr, return_value);
                }
                Number::Fixnum(fixnum) => self.machine_st.unify_fixnum(fixnum, return_value),
            },
            Value::Struct(name, args) => {
                let struct_value =
                    resource_error_call_result!(self.machine_st, self.build_struct(name, args));

                unify!(self.machine_st, return_value, struct_value);
            }
            Value::CString(cstr) => {
                let str_cell = resource_error_call_result!(
                    self.machine_st,
                    self.machine_st.heap.allocate_cstr(cstr.to_str().unwrap())
                );

                unify!(self.machine_st, str_cell, return_value);
            }
        }
        Ok(())
    }

    #[cfg(feature = "ffi")]
    fn build_struct(&mut self, name: Atom, mut args: Vec<Value>) -> Result<HeapCellValue, usize> {
        args.insert(0, Value::CString(CString::new(&*name.as_str()).unwrap()));

        let cells: Vec<_> = args
            .into_iter()
            .map(|val| {
                Ok(match val {
                    Value::Number(n) => match n {
                        Number::Float(OrderedFloat(f)) => {
                            HeapCellValue::from(float_alloc!(f, self.machine_st.arena))
                        }
                        _ => integer_as_cell!(n),
                    },
                    Value::CString(cstr) => atom_as_cell!(AtomTable::build_with(
                        &self.machine_st.atom_tbl,
                        &cstr.into_string().unwrap()
                    )),
                    Value::Struct(name, struct_args) => self.build_struct(name, struct_args)?,
                })
            })
            .collect::<Result<_, usize>>()?;

        sized_iter_to_heap_list(&mut self.machine_st.heap, cells.len(), cells.into_iter())
    }

    #[inline(always)]
    pub(crate) fn define_foreign_struct(&mut self) -> CallResult {
        fn stub_gen() -> MachineStub {
            functor_stub(atom!("$define_foreign_struct"), 2)
        }

        #[cfg(feature = "ffi")]
        {
            let struct_name_arg = self.machine_st.store(self.deref_register(1));
            let fields_reg = self.deref_register(2);
            if let Some(struct_name) = struct_name_arg.to_atom() {
                let fields: Vec<Atom> = match self.machine_st.try_from_list(fields_reg, stub_gen) {
                    Ok(addrs) => {
                        let mut args = Vec::new();
                        for heap_cell in addrs {
                            let arg_cell = self.machine_st.store(self.machine_st.deref(heap_cell));
                            let Some(arg) = arg_cell.to_atom() else {
                                let err = if arg_cell.is_var() {
                                    self.machine_st.instantiation_error()
                                } else {
                                    self.machine_st.type_error(ValidType::Atom, heap_cell)
                                };

                                return Err(self.machine_st.error_form(err, stub_gen()));
                            };

                            args.push(arg);
                        }
                        args
                    }
                    Err(e) => return Err(e),
                };
                self.foreign_function_table
                    .define_struct(struct_name, fields)
                    .map_err(|err| {
                        let ffi_error = self.machine_st.ffi_error(err);
                        self.machine_st.error_form(ffi_error, stub_gen())
                    })?;
                Ok(())
            } else {
                let err = self.machine_st.type_error(ValidType::Atom, struct_name_arg);
                Err(self.machine_st.error_form(err, stub_gen()))
            }
        }

        #[cfg(not(feature = "ffi"))]
        {
            let err = self.machine_st.missing_feature_error(atom!("ffi"));
            Err(self.machine_st.error_form(err, stub_gen()))
        }
    }

    pub(crate) fn ffi_allocate(&mut self) -> CallResult {
        fn stub_gen() -> MachineStub {
            functor_stub(atom!("$ffi_allocate"), 4)
        }

        #[cfg(feature = "ffi")]
        {
            let allocator = self.deref_register(1);
            let ffi_type_arg = self.deref_register(2);
            let ffi_type = ffi_type_arg.to_atom().unwrap();
            let args = self.deref_register(3);
            let return_value = self.deref_register(4);

            let allocator = FfiAllocator::try_from(allocator.to_atom().unwrap()).map_err(|_| {
                let machine_error = self
                    .machine_st
                    .domain_error(DomainErrorType::Allocator, allocator);
                self.machine_st.error_form(machine_error, stub_gen())
            })?;

            let args = self.map_ffi_arg(args, stub_gen)?;

            let value = match self.foreign_function_table.allocate(
                allocator,
                ffi_type,
                args,
                &mut self.machine_st.arena,
            ) {
                Ok(value) => value,
                Err(ffi_error) => {
                    let machine_error = self.machine_st.ffi_error(ffi_error);
                    return Err(self.machine_st.error_form(machine_error, stub_gen()));
                }
            };

            self.unify_ffi_result(return_value, value)
        }

        #[cfg(not(feature = "ffi"))]
        {
            let err = self.machine_st.missing_feature_error(atom!("ffi"));
            Err(self.machine_st.error_form(err, stub_gen()))
        }
    }

    pub(crate) fn ffi_read_ptr(&mut self) -> CallResult {
        fn stub_gen() -> MachineStub {
            functor_stub(atom!("$ffi_read_ptr"), 3)
        }

        #[cfg(feature = "ffi")]
        {
            let ffi_type_arg = self.deref_register(1);
            let ffi_type = ffi_type_arg.to_atom().unwrap();
            let ptr = self.deref_register(2);
            let return_value = self.deref_register(3);

            let ptr = self.map_ffi_arg(ptr, stub_gen)?;

            let value = self
                .foreign_function_table
                .read_ptr(ffi_type, ptr, &mut self.machine_st.arena)
                .map_err(|ffi_error| {
                    let machine_error = self.machine_st.ffi_error(ffi_error);
                    self.machine_st.error_form(machine_error, stub_gen())
                })?;

            self.unify_ffi_result(return_value, value)
        }

        #[cfg(not(feature = "ffi"))]
        {
            let err = self.machine_st.missing_feature_error(atom!("ffi"));
            Err(self.machine_st.error_form(err, stub_gen()))
        }
    }

    pub(crate) fn ffi_deallocate(&mut self) -> CallResult {
        fn stub_gen() -> MachineStub {
            functor_stub(atom!("$ffi_deallocate"), 3)
        }

        #[cfg(feature = "ffi")]
        {
            let allocator = self.deref_register(1);
            let ffi_type_arg = self.deref_register(2);
            let ffi_type = ffi_type_arg.to_atom().unwrap();
            let ptr = self.deref_register(3);

            let allocator = FfiAllocator::try_from(allocator.to_atom().unwrap()).map_err(|_| {
                let machine_error = self
                    .machine_st
                    .domain_error(DomainErrorType::Allocator, allocator);
                self.machine_st.error_form(machine_error, stub_gen())
            })?;

            let ptr = self.map_ffi_arg(ptr, stub_gen)?;

            match self
                .foreign_function_table
                .deallocate(allocator, ffi_type, ptr)
            {
                Ok(value) => value,
                Err(ffi_error) => {
                    let machine_error = self.machine_st.ffi_error(ffi_error);
                    return Err(self.machine_st.error_form(machine_error, stub_gen()));
                }
            }
            Ok(())
        }

        #[cfg(not(feature = "ffi"))]
        {
            let err = self.machine_st.missing_feature_error(atom!("ffi"));
            Err(self.machine_st.error_form(err, stub_gen()))
        }
    }

    #[cfg(not(target_arch = "wasm32"))]
    #[inline(always)]
    pub(crate) fn js_eval(&mut self) -> CallResult {
        unimplemented!()
    }

    #[cfg(target_arch = "wasm32")]
    #[inline(always)]
    pub(crate) fn js_eval(&mut self) -> CallResult {
        let code = self.deref_register(1);
        let result_reg = self.deref_register(2);
        if let Some(code) = self.machine_st.value_to_str_like(code) {
            match js_sys::eval(&code.as_str()) {
                Ok(result) => self.unify_js_value(result, result_reg)?,
                Err(result) => self.unify_js_value(result, result_reg)?,
            };

            return Ok(());
        }
        self.machine_st.fail = true;
        Ok(())
    }

    #[cfg(target_arch = "wasm32")]
    fn unify_js_value(
        &mut self,
        result: wasm_bindgen::JsValue,
        result_reg: HeapCellValue,
    ) -> CallResult {
        match result.as_bool() {
            Some(result) => match result {
                true => self.machine_st.unify_atom(atom!("true"), result_reg),
                false => self.machine_st.unify_atom(atom!("false"), result_reg),
            },
            None => match result.as_f64() {
                Some(result) => {
                    let n = float_alloc!(result, self.machine_st.arena);
                    self.machine_st.unify_f64(n, result_reg);
                }
                None => match result.as_string() {
                    Some(result) => {
                        resource_error_call_result!(
                            self.machine_st,
                            self.machine_st.heap.allocate_cstr(result.as_str())
                        );
                    }
                    None => {
                        if result.is_null() {
                            self.machine_st.unify_atom(atom!("null"), result_reg);
                        } else if result.is_undefined() {
                            self.machine_st.unify_atom(atom!("undefined"), result_reg);
                        } else if result.is_symbol() {
                            self.machine_st.unify_atom(atom!("js_symbol"), result_reg);
                        } else if result.is_object() {
                            self.machine_st.unify_atom(atom!("js_object"), result_reg);
                        } else if result.is_array() {
                            self.machine_st.unify_atom(atom!("js_array"), result_reg);
                        } else if result.is_function() {
                            self.machine_st.unify_atom(atom!("js_function"), result_reg);
                        } else if result.is_bigint() {
                            self.machine_st.unify_atom(atom!("js_bigint"), result_reg);
                        } else {
                            self.machine_st
                                .unify_atom(atom!("js_unknown_type"), result_reg);
                        }
                    }
                },
            },
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn argv(&mut self) -> CallResult {
        let args = self.deref_register(1);
        let mut args_pstrs = vec![];

        for arg in env::args() {
            let pstr_cell = resource_error_call_result!(
                self.machine_st,
                self.machine_st.heap.allocate_cstr(&arg)
            );

            args_pstrs.push(pstr_cell);
        }

        let list_cell = resource_error_call_result!(
            self.machine_st,
            sized_iter_to_heap_list(
                &mut self.machine_st.heap,
                args_pstrs.len(),
                args_pstrs.into_iter(),
            )
        );

        unify!(self.machine_st, args, list_cell);
        Ok(())
    }

    #[inline(always)]
    pub(crate) fn current_time(&mut self) {
        let timestamp = self.systemtime_to_timestamp(SystemTime::now());
        let cstr_cell = step_or_resource_error!(
            self.machine_st,
            self.machine_st.heap.allocate_cstr(&timestamp)
        );

        unify!(self.machine_st, cstr_cell, self.machine_st.registers[1]);
    }

    #[inline(always)]
    pub(crate) fn open(&mut self) -> CallResult {
        let alias = self.machine_st.registers[4];
        let eof_action = self.machine_st.registers[5];
        let reposition = self.machine_st.registers[6];
        let stream_type = self.machine_st.registers[7];

        let options =
            self.machine_st
                .get_stream_options(alias, eof_action, reposition, stream_type);
        let src_sink = self.deref_register(1);

        if let Some(file_spec) = self.machine_st.value_to_str_like(src_sink) {
            let file_spec = file_spec.as_atom(&self.machine_st.atom_tbl);

            let mut stream =
                self.machine_st
                    .stream_from_file_spec(file_spec, &mut self.indices, &options)?;

            *stream.options_mut() = options;

            self.indices
                .add_stream(stream, atom!("open"), 4)
                .map_err(|stub_gen| stub_gen(&mut self.machine_st))?;

            let stream_var = self.deref_register(3);
            self.machine_st
                .bind(stream_var.as_var().unwrap(), stream.into());
        } else {
            let err = self
                .machine_st
                .domain_error(DomainErrorType::SourceSink, src_sink);
            let stub = functor_stub(atom!("open"), 4);

            return Err(self.machine_st.error_form(err, stub));
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn op_declaration(&mut self) -> CallResult {
        let priority = self.deref_register(1);
        let specifier = cell_as_atom_cell!(self.deref_register(2)).get_name();

        let priority = match Number::try_from((priority, &self.machine_st.arena.f64_tbl)) {
            Ok(Number::Integer(n)) => {
                let n: u16 = (&*n).try_into().unwrap();
                n
            }
            Ok(Number::Fixnum(n)) => u16::try_from(n.get_num()).unwrap(),
            _ => {
                unreachable!();
            }
        };

        let op = read_heap_cell!(self.deref_register(3),
            /*
            (HeapCellValueTag::Char, c) => {
                AtomTable::build_with(&self.machine_st.atom_tbl, &c.to_string())
            }
            */
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

        let result = to_op_decl_spec(specifier)
            .map_err(SessionError::from)
            .map(|specifier| to_op_decl(priority, specifier, op))
            .and_then(|mut op_decl| {
                if op_decl.op_desc.get_prec() == 0 {
                    op_decl.remove(&mut self.indices.op_dir);
                    Ok(())
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
        let stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices,
            atom!("open"),
            4,
        )?;

        let alias = self.machine_st.registers[2];
        let eof_action = self.machine_st.registers[3];
        let reposition = self.machine_st.registers[4];
        let stream_type = self.machine_st.registers[5];

        let new_options =
            self.machine_st
                .get_stream_options(alias, eof_action, reposition, stream_type);
        self.indices.update_stream_options(stream, |options| {
            *options = new_options;
        });

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn truncate_if_no_lifted_heap_growth_diff(&mut self) {
        self.machine_st
            .truncate_if_no_lifted_heap_diff(|h| heap_loc_as_cell!(h))
    }

    #[inline(always)]
    pub(crate) fn truncate_if_no_lifted_heap_growth(&mut self) {
        self.machine_st
            .truncate_if_no_lifted_heap_diff(|_| empty_list_as_cell!())
    }

    #[inline(always)]
    pub(crate) fn get_attributed_variable_list(&mut self) {
        let attr_var = self.deref_register(1);
        let attr_var_list = read_heap_cell!(attr_var,
            (HeapCellValueTag::AttrVar, h) => {
                h+1
            }
            (HeapCellValueTag::Var, h) => {
                h
            }
            _ => {
                self.machine_st.fail = true;
                return;
            }
        );

        let list_addr = self.deref_register(2);
        self.machine_st
            .bind(Ref::heap_cell(attr_var_list), list_addr);
    }

    #[inline(always)]
    pub(crate) fn get_from_attributed_variable_list(&mut self) {
        let attr_var = self.deref_register(1);
        let attr = self.deref_register(3);
        let attr_var_list = read_heap_cell!(attr_var,
            (HeapCellValueTag::AttrVar, h) => {
                self.machine_st.heap[h+1]
            }
            _ => {
                self.machine_st.fail = true;
                return;
            }
        );

        let module = self.deref_register(2);

        match self.match_attribute(attr_var_list, module, attr) {
            Some(AttrListMatch {
                match_site: MatchSite::Match(match_site),
                ..
            }) => {
                let list_head = self.machine_st.heap[match_site];

                if list_head.get_value() as usize == match_site {
                    // at the end of the list, no match found in this case.
                    self.machine_st.fail = true;
                } else {
                    let (_, qualified_goal) = self.machine_st.strip_module(list_head);

                    unify!(self.machine_st, qualified_goal, attr);
                }
            }
            _ => {
                self.machine_st.fail = true;
            }
        }
    }

    #[inline(always)]
    pub(crate) fn get_attr_var_queue_delimiter(&mut self) {
        let addr = self.deref_register(1);

        /* FIXME this is not safe */
        let value = unsafe {
            Fixnum::build_with_unchecked(self.machine_st.attr_var_init.attr_var_queue.len() as i64)
        };

        self.machine_st.unify_fixnum(value, addr);
    }

    #[inline(always)]
    pub(crate) fn get_attr_var_queue_beyond(&mut self) {
        let addr = self.deref_register(1);

        let b = match Number::try_from((addr, &self.machine_st.arena.f64_tbl)) {
            Ok(Number::Integer(n)) => {
                let value: usize = (&*n).try_into().unwrap();
                Some(value)
            }
            Ok(Number::Fixnum(n)) => usize::try_from(n.get_num()).ok(),
            _ => {
                self.machine_st.fail = true;
                return;
            }
        };

        if let Some(b) = b {
            let attr_vars = self.machine_st.gather_attr_vars_created_since(b);

            let var_list_addr = step_or_resource_error!(
                self.machine_st,
                sized_iter_to_heap_list(
                    &mut self.machine_st.heap,
                    attr_vars.len(),
                    attr_vars.into_iter(),
                )
            );

            let list_addr = self.machine_st.registers[2];
            unify!(self.machine_st, var_list_addr, list_addr);
        }
    }

    #[inline(always)]
    pub(crate) fn delete_from_attributed_variable_list(&mut self) {
        let attr_var = self.deref_register(1);
        let attr = self.deref_register(3);
        let attr_var_list = read_heap_cell!(attr_var,
            (HeapCellValueTag::AttrVar, h) => {
                h + 1
            }
            _ => {
                return;
            }
        );

        let module = self.deref_register(2);

        if let Some(AttrListMatch {
            prev_tail,
            match_site: MatchSite::Match(match_site),
        }) = self.match_attribute(self.machine_st.heap[attr_var_list], module, attr)
        {
            let prev_tail = if let Some(prev_tail) = prev_tail {
                // not at the head.
                prev_tail
            } else {
                if self.machine_st.heap[match_site + 1].is_var() {
                    let h = attr_var.get_value() as usize;

                    self.machine_st.heap[h] = heap_loc_as_cell!(h);
                    self.machine_st.trail(TrailRef::Ref(Ref::attr_var(h)));
                }

                // at the head.
                attr_var_list
            };

            if self.machine_st.heap[match_site + 1].get_tag() == HeapCellValueTag::Lis {
                let prev_tail_value = self.machine_st.heap[match_site + 1].get_value();
                self.machine_st.heap[prev_tail].set_value(prev_tail_value);
            } else {
                self.machine_st.heap[prev_tail] = heap_loc_as_cell!(prev_tail);
            }

            self.machine_st
                .trail(TrailRef::AttrVarListLink(prev_tail, match_site));
        }
    }

    #[inline(always)]
    pub(crate) fn put_to_attributed_variable_list(&mut self) {
        let attr_var = self.deref_register(1);
        let attr = self.deref_register(3);
        let attr_var_list_result =
            step_or_resource_error!(self.machine_st, self.machine_st.get_attr_var_list(attr_var));

        let attr_var_list = match attr_var_list_result {
            Some(h) => h,
            None => {
                self.machine_st.fail = true;
                return;
            }
        };

        let module = self.deref_register(2);

        /*
         * How to handle attribute trailing using just AttrVarListLink (which
         * should be re-named to something more general) in unwind_trail:
         *
         * Given AttrVarListLink(h, l):
         *
         * 1. Check cell at offset l.
         * 2. If h == l, set heap[h] = heap_loc_as_cell!(h).
         * 3. If cell is a Var, set heap[h] = list_loc_as_cell!(l).
         * 4. Otherwise, cell points to an element of the list which is therefore
         *    an atom or str. Set heap[h] accordingly.
         *
         * For this to work, all elements of attributed variable lists must be
         * heap cell locs pointing to later elements in the heap, either atoms (0-arity)
         * or str cells (> 0-arity).
         */

        let module_functor = functor!(atom!(":"), [cell(module), cell(attr)]);
        let h = self.machine_st.heap.cell_len();

        step_or_resource_error!(
            self.machine_st,
            self.machine_st.heap.push_cell(str_loc_as_cell!(h + 1))
        );

        let mut functor_writer = Heap::functor_writer(module_functor);
        step_or_resource_error!(self.machine_st, functor_writer(&mut self.machine_st.heap));

        match self.match_attribute(self.machine_st.heap[attr_var_list], module, attr) {
            Some(AttrListMatch { match_site, .. }) => {
                let (match_site, l) = match match_site {
                    MatchSite::NoMatchVarTail(match_site) => {
                        let l = self.machine_st.heap[match_site].get_value();

                        // at the end of the (non-empty) list here.
                        self.machine_st.heap[match_site] = list_loc_as_cell!(h + 4);

                        let mut writer = step_or_resource_error!(
                            self.machine_st,
                            self.machine_st.heap.reserve(2)
                        );

                        writer.write_with(|section| {
                            section.push_cell(heap_loc_as_cell!(h));
                            section.push_cell(heap_loc_as_cell!(h + 5));
                        });

                        (match_site, l)
                    }
                    MatchSite::Match(match_site) => {
                        let l = self.machine_st.heap[match_site].get_value();
                        self.machine_st.heap[match_site].set_value(h as u64);

                        (match_site, l)
                    }
                };

                self.machine_st
                    .trail(TrailRef::AttrVarListLink(match_site, l as usize));
            }
            None => {
                // the list is empty.
                self.machine_st.heap[attr_var_list] = list_loc_as_cell!(h + 4);

                let mut writer =
                    step_or_resource_error!(self.machine_st, self.machine_st.heap.reserve(2));

                writer.write_with(|section| {
                    section.push_cell(heap_loc_as_cell!(h));
                    section.push_cell(heap_loc_as_cell!(h + 5));
                });

                self.machine_st
                    .attr_var_init
                    .attr_var_queue
                    .push(attr_var_list - 1);
                self.machine_st
                    .trail(TrailRef::AttrVarListLink(attr_var_list, attr_var_list));
            }
        }
    }

    fn match_attribute(
        &self,
        mut attrs_list: HeapCellValue,
        module: HeapCellValue,
        attr: HeapCellValue,
    ) -> Option<AttrListMatch> {
        let (name, arity) = match self.machine_st.name_and_arity_from_heap(attr) {
            Some(key) => key,
            None => {
                return None;
            }
        };

        let mut prev_tail = None;

        while let HeapCellValueTag::Lis = attrs_list.get_tag() {
            let mut list_head = self.machine_st.heap[attrs_list.get_value() as usize];

            loop {
                read_heap_cell!(list_head,
                    (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
                        debug_assert!(list_head != self.machine_st.heap[h]);
                        list_head = self.machine_st.heap[h];
                    }
                    (HeapCellValueTag::Str | HeapCellValueTag::Atom) => {
                        let (quantification, qualified_goal) = self.machine_st.strip_module(list_head);

                        let (t_name, t_arity) = self.machine_st
                            .name_and_arity_from_heap(qualified_goal)
                            .unwrap();

                        if Some(module) == quantification.specified() &&
                            name == t_name &&
                            arity == t_arity
                        {
                            return Some(AttrListMatch {
                                match_site: MatchSite::Match(attrs_list.get_value() as usize),
                                prev_tail,
                            });
                        }

                        break;
                    }
                    _ => {
                        break;
                    }
                );
            }

            let tail_loc = attrs_list.get_value() as usize + 1;
            prev_tail = Some(tail_loc);

            // do the work of self.store(self.deref(...)) but inline it
            // for speed and simplify it.
            let mut list_tail = self.machine_st.heap[tail_loc];

            loop {
                read_heap_cell!(list_tail,
                    (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
                        if list_tail != self.machine_st.heap[h] {
                            list_tail = self.machine_st.heap[h];
                        } else {
                            return Some(AttrListMatch {
                                match_site: MatchSite::NoMatchVarTail(h),
                                prev_tail,
                            });
                        }
                    }
                    (HeapCellValueTag::Lis) => {
                        attrs_list = list_tail;
                        break;
                    }
                    _ => {
                        unreachable!()
                    }
                );
            }
        }

        None
    }

    #[inline(always)]
    pub(crate) fn get_continuation_chunk(&mut self) {
        let e = self.deref_register(1);
        let e = unsafe { e.to_fixnum_or_cut_point_unchecked() }.get_num() as usize;
        let h = self.machine_st.heap.cell_len();

        let p_functor_cell = self.deref_register(2);
        let num_cells = self.machine_st.stack.index_and_frame(e).prelude.num_cells;

        let mut writer =
            step_or_resource_error!(self.machine_st, self.machine_st.heap.reserve(2 + num_cells));

        writer.write_with(|section| {
            section.push_cell(atom_as_cell!(atom!("cont_chunk"), 1 + num_cells));
            section.push_cell(p_functor_cell);

            for idx in 1..=num_cells {
                let mut stack_offset = stack_loc!(AndFrame, e, idx);
                let mut addr = self.machine_st.stack[stack_offset];

                while addr.get_tag() == HeapCellValueTag::StackVar {
                    stack_offset = addr.get_value() as usize;

                    if self.machine_st.stack[stack_offset] == addr {
                        break;
                    }

                    addr = self.machine_st.stack[stack_offset];
                }

                if addr.get_tag() == HeapCellValueTag::StackVar {
                    section.push_cell(heap_loc_as_cell!(h + 1 + idx));
                    self.machine_st.stack[stack_offset] = heap_loc_as_cell!(h + 1 + idx);

                    // have to inline the TrailRef::Ref(RefTag::StackCell) case of MachineState::trail
                    // here to get around the borrow checker.
                    if stack_offset < self.machine_st.b {
                        self.machine_st.trail.push(TrailEntry::build_with(
                            TrailEntryTag::TrailedStackVar,
                            stack_offset as u64,
                        ));

                        self.machine_st.tr += 1;
                    }
                } else {
                    section.push_cell(addr);
                }
            }
        });

        let chunk = str_loc_as_cell!(h);
        unify!(self.machine_st, self.machine_st.registers[3], chunk);
    }

    #[inline(always)]
    pub(crate) fn get_lifted_heap_from_offset_diff(&mut self) {
        let lh_offset = self.machine_st.registers[1];
        let lh_offset = unsafe {
            self.machine_st
                .store(self.machine_st.deref(lh_offset))
                .to_fixnum_or_cut_point_unchecked()
        }
        .get_num() as usize;

        if lh_offset >= self.machine_st.lifted_heap.cell_len() {
            let solutions = self.machine_st.registers[2];
            let diff = self.machine_st.registers[3];

            unify_fn!(self.machine_st, solutions, diff);
        } else {
            let h = self.machine_st.heap.cell_len();
            self.machine_st.copy_lifted_heap_from_offset(h, lh_offset);

            let diff = self.machine_st.registers[3];
            unify_fn!(
                self.machine_st,
                diff,
                self.machine_st.heap.last_cell().unwrap()
            );

            self.machine_st.lifted_heap.truncate(lh_offset);

            let solutions = self.machine_st.registers[2];
            unify_fn!(self.machine_st, heap_loc_as_cell!(h), solutions);
        }
    }

    #[inline(always)]
    pub(crate) fn get_lifted_heap_from_offset(&mut self) {
        let lh_offset = self.machine_st.registers[1];
        let lh_offset = unsafe {
            self.machine_st
                .store(self.machine_st.deref(lh_offset))
                .to_fixnum_or_cut_point_unchecked()
        }
        .get_num() as usize;

        if lh_offset >= self.machine_st.lifted_heap.cell_len() {
            let solutions = self.machine_st.registers[2];
            unify_fn!(self.machine_st, solutions, empty_list_as_cell!());
        } else {
            let h = self.machine_st.heap.cell_len();

            self.machine_st.copy_lifted_heap_from_offset(h, lh_offset);
            self.machine_st.lifted_heap.truncate(lh_offset);

            let solutions = self.machine_st.registers[2];
            unify_fn!(self.machine_st, heap_loc_as_cell!(h), solutions);
        }
    }

    #[inline(always)]
    pub(crate) fn get_double_quotes(&mut self) {
        let a1 = self.deref_register(1);

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
    pub(crate) fn get_unknown(&mut self) {
        let a1 = self.deref_register(1);

        self.machine_st.unify_atom(
            match self.machine_st.flags.unknown {
                Unknown::Error => atom!("error"),
                Unknown::Fail => atom!("fail"),
                Unknown::Warn => atom!("warning"),
            },
            a1,
        );
    }

    #[inline(always)]
    pub(crate) fn get_scc_cleaner(&mut self) {
        let dest = self.machine_st.registers[1];

        if let Some((addr, b_cutoff, prev_block)) = self.machine_st.cont_pts.pop() {
            let b = self
                .machine_st
                .stack
                .index_or_frame(self.machine_st.b)
                .prelude
                .b;

            if b <= b_cutoff {
                self.machine_st.scc_block = prev_block;

                if let Some(r) = dest.as_var() {
                    self.machine_st.bind(r, addr);
                    return;
                }
            } else {
                self.machine_st.cont_pts.push((addr, b_cutoff, prev_block));
            }
        }

        self.machine_st.fail = true;
    }

    #[inline(always)]
    pub(crate) fn halt(&mut self) -> std::process::ExitCode {
        let code = self.deref_register(1);

        let code = match Number::try_from((code, &self.machine_st.arena.f64_tbl)) {
            Ok(Number::Fixnum(n)) => u8::try_from(n.get_num()).unwrap(),
            Ok(Number::Integer(n)) => {
                let n: u8 = (&*n).try_into().unwrap();
                n
            }
            Ok(Number::Rational(r)) => {
                // n has already been confirmed as an integer, and
                // internally, Rational is assumed reduced, so its
                // denominator must be 1.
                r.numerator().try_into().unwrap()
            }
            _ => {
                unreachable!()
            }
        };

        std::process::ExitCode::from(code)
    }

    #[inline(always)]
    pub(crate) fn install_scc_cleaner(&mut self) {
        let addr = self.machine_st.registers[1];
        let b = self.machine_st.b;
        let prev_block = self.machine_st.scc_block;

        self.machine_st.run_cleaners_fn = Machine::run_cleaners;
        self.machine_st.scc_block = b;
        self.machine_st.cont_pts.push((addr, b, prev_block));
    }

    #[inline(always)]
    pub(crate) fn install_inference_counter(&mut self) -> CallResult {
        // A1 = B, A2 = L
        let a1 = self.deref_register(1);
        let a2 = self.deref_register(2);

        let n = match Number::try_from((a2, &self.machine_st.arena.f64_tbl)) {
            Ok(Number::Fixnum(bp)) => Integer::from(bp.get_num() as usize),
            Ok(Number::Integer(n)) => (*n).clone(),
            _ => {
                let stub = functor_stub(atom!("call_with_inference_limit"), 3);
                let err = self.machine_st.type_error(ValidType::Integer, a2);
                return Err(self.machine_st.error_form(err, stub));
            }
        };

        let bp = unsafe { a1.to_fixnum_or_cut_point_unchecked() }.get_num() as usize;
        let a3 = self.deref_register(3);

        let count = self.machine_st.cwil.add_limit(n, bp).clone();
        self.inference_count(a3, count);

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn inference_count(&mut self, count_var: HeapCellValue, count: Integer) {
        if let Some(value) = <&Integer as TryInto<i64>>::try_into(&count)
            .ok()
            .and_then(|i| Fixnum::build_with_checked(i).ok())
        {
            self.machine_st.unify_fixnum(value, count_var);
        } else {
            let count = arena_alloc!(count, &mut self.machine_st.arena);
            self.machine_st.unify_big_int(count, count_var);
        }
    }

    #[inline(always)]
    pub(crate) fn module_exists(&mut self) {
        let module = self.deref_register(1);
        let module_name = cell_as_atom!(module);

        self.machine_st.fail = !self.indices.modules.contains_key(&module_name);
    }

    pub(crate) fn predicate_defined(&mut self) -> bool {
        let module_name = cell_as_atom!(self.deref_register(1));
        let name = cell_as_atom!(self.deref_register(2));
        let a3 = self.deref_register(3);

        let arity = match Number::try_from((a3, &self.machine_st.arena.f64_tbl)) {
            Ok(Number::Fixnum(n)) => n.get_num() as usize,
            Ok(Number::Integer(n)) => {
                let result = (&*n).try_into();

                if let Ok(value) = result {
                    value
                } else {
                    return false;
                }
            }
            _ => {
                unreachable!()
            }
        };

        self.indices
            .get_predicate_code_index(name, arity, module_name)
            .map(|idx| {
                self.machine_st
                    .arena
                    .code_index_tbl
                    .get_entry(idx.into())
                    .local()
                    .is_some()
            })
            .unwrap_or(false)
    }

    #[inline(always)]
    pub(crate) fn no_such_predicate(&mut self) -> CallResult {
        let module_name = cell_as_atom!(self.deref_register(1));
        let head = self.deref_register(2);

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
                        .map(|idx| self.machine_st
                             .arena
                             .code_index_tbl
                             .get_entry(idx.into()))
                        .unwrap_or(IndexPtr::dynamic_undefined());

                    !matches!(index.tag(), IndexPtrTag::DynamicUndefined | IndexPtrTag::Undefined)
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
                        .map(|idx| self.machine_st
                             .arena
                             .code_index_tbl
                             .get_entry(idx.into()))
                        .unwrap_or(IndexPtr::dynamic_undefined());

                    !matches!(index.tag(), IndexPtrTag::DynamicUndefined)
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
        // registers[1] MUST NOT be dereferenced here. the original
        // AttrVar binding site must be preserved.
        let var = self.machine_st.registers[1];
        let value = self.deref_register(2);

        debug_assert_eq!(HeapCellValueTag::AttrVar, var.get_tag());
        self.machine_st.heap[var.get_value() as usize] = value;
    }

    #[inline(always)]
    pub(super) fn restore_instr_at_verify_attr_interrupt(&mut self) {
        match &self.code[VERIFY_ATTR_INTERRUPT_LOC] {
            &Instruction::VerifyAttrInterrupt(_) => {}
            _ => {
                let instr = mem::replace(
                    &mut self.code[VERIFY_ATTR_INTERRUPT_LOC],
                    Instruction::VerifyAttrInterrupt(0),
                );

                self.code[self.machine_st.attr_var_init.cp] = instr;
            }
        }
    }

    #[inline(always)]
    pub(crate) fn reset_attr_var_state(&mut self, queue_len: usize) {
        self.restore_instr_at_verify_attr_interrupt();
        self.machine_st.attr_var_init.reset(queue_len);
    }

    #[inline(always)]
    pub(crate) fn remove_call_policy_check(&mut self) {
        let bp =
            unsafe { self.deref_register(1).to_fixnum_or_cut_point_unchecked() }.get_num() as usize;

        if bp == self.machine_st.b && self.machine_st.cwil.is_empty() {
            self.machine_st.cwil.reset();
        }
    }

    #[inline(always)]
    pub(crate) fn remove_inference_counter(&mut self) {
        let a1 = self.deref_register(1);
        let a2 = self.deref_register(2);

        let block = unsafe { a1.to_fixnum_or_cut_point_unchecked() }.get_num() as usize;
        let count = self.machine_st.cwil.remove_limit(block).clone();
        if let Ok(value) = Fixnum::build_with_checked(&count) {
            self.machine_st.unify_fixnum(value, a2);
        } else {
            let count = arena_alloc!(count.clone(), &mut self.machine_st.arena);
            self.machine_st.unify_big_int(count, a2);
        }
    }

    #[inline(always)]
    pub(crate) fn return_from_verify_attr(&mut self) {
        self.restore_instr_at_verify_attr_interrupt();

        let e = self.machine_st.e;
        let frame_len = self.machine_st.stack.index_and_frame(e).prelude.num_cells;

        for i in 1..frame_len - 2 {
            self.machine_st.registers[i] = self.machine_st.stack[stack_loc!(AndFrame, e, i)];
        }

        self.machine_st.b0 = unsafe {
            self.machine_st.stack[stack_loc!(AndFrame, e, frame_len - 2)]
                .to_fixnum_or_cut_point_unchecked()
        }
        .get_num() as usize;

        self.machine_st.num_of_args = unsafe {
            self.machine_st.stack[stack_loc!(AndFrame, e, frame_len - 1)]
                .to_fixnum_or_cut_point_unchecked()
        }
        .get_num() as usize;

        let p = unsafe {
            self.machine_st.stack[stack_loc!(AndFrame, e, frame_len)]
                .to_fixnum_or_cut_point_unchecked()
        }
        .get_num() as usize;

        self.machine_st.deallocate();
        self.machine_st.p = p;
    }

    #[inline(always)]
    pub(crate) fn restore_cut_policy(&mut self) {
        if self.machine_st.cont_pts.is_empty() {
            self.machine_st.run_cleaners_fn = |_| false;
        }
    }

    #[inline(always)]
    pub(crate) fn set_cut_point(&mut self, r: RegType) -> bool {
        let cp = self
            .machine_st
            .store(self.machine_st.deref(self.machine_st[r]));
        self.machine_st.cut_body(cp);

        (self.machine_st.run_cleaners_fn)(self)
    }

    #[inline(always)]
    pub(crate) fn set_cut_point_by_default(&mut self, r: RegType) {
        let cp = self
            .machine_st
            .store(self.machine_st.deref(self.machine_st[r]));
        self.machine_st.cut_body(cp);
    }

    #[inline(always)]
    pub(crate) fn set_input(&mut self) -> CallResult {
        let addr = self.deref_register(1);

        let stream =
            self.machine_st
                .get_stream_or_alias(addr, &self.indices, atom!("set_input"), 1)?;

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
        self.indices.set_stream(atom!("user_input"), stream);
        Ok(())
    }

    #[inline(always)]
    pub(crate) fn set_output(&mut self) -> CallResult {
        let addr = self.deref_register(1);
        let stream =
            self.machine_st
                .get_stream_or_alias(addr, &self.indices, atom!("set_output"), 1)?;

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
        self.indices.set_stream(atom!("user_output"), stream);
        Ok(())
    }

    #[inline(always)]
    pub(crate) fn set_double_quotes(&mut self) {
        let atom = cell_as_atom!(self.deref_register(1));

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
    pub(crate) fn set_unknown(&mut self) {
        let atom = cell_as_atom!(self.deref_register(1));

        self.machine_st.flags.unknown = match atom {
            atom!("error") => Unknown::Error,
            atom!("fail") => Unknown::Fail,
            atom!("warning") => Unknown::Warn,
            _ => {
                self.machine_st.fail = true;
                return;
            }
        };
    }

    #[inline(always)]
    pub(crate) fn inference_level(&mut self) {
        let a1 = self.deref_register(1);
        let a2 = self.deref_register(2);

        let bp = unsafe { a2.to_fixnum_or_cut_point_unchecked() }.get_num() as usize;
        let prev_b = self
            .machine_st
            .stack
            .index_or_frame(self.machine_st.b)
            .prelude
            .b;

        if prev_b <= bp {
            self.machine_st.unify_atom(atom!("!"), a1)
        } else {
            self.machine_st.unify_atom(atom!("true"), a1);
        }
    }

    #[inline(always)]
    pub(crate) fn inference_limit_exceeded(&mut self) {
        self.machine_st.fail = !self.machine_st.cwil.inference_limit_exceeded;
    }

    #[inline(always)]
    pub(crate) fn clean_up_block(&mut self) {
        let nb = self.deref_register(1);
        let nb = unsafe { nb.to_fixnum_or_cut_point_unchecked() }.get_num() as usize;

        let b = self.machine_st.b;

        if nb > 0 && self.machine_st.stack.index_or_frame(b).prelude.b == nb {
            self.machine_st.b = self.machine_st.stack.index_or_frame(nb).prelude.b;
        }
    }

    #[inline(always)]
    pub(crate) fn get_ball(&mut self) {
        let addr = self.deref_register(1);
        let h = if !self.machine_st.ball.stub.is_empty() {
            step_or_resource_error!(
                self.machine_st,
                self.machine_st
                    .ball
                    .copy_and_align_to(&mut self.machine_st.heap)
            )
        } else {
            self.machine_st.fail = true;
            return;
        };

        match addr.as_var() {
            Some(r) => self.machine_st.bind(r, self.machine_st.heap[h]),
            _ => self.machine_st.fail = true,
        };
    }

    #[inline(always)]
    pub(crate) fn push_ball_stack(&mut self) {
        if !self.machine_st.ball.stub.is_empty() {
            self.machine_st
                .ball_stack
                .push(mem::replace(&mut self.machine_st.ball, Ball::new()));
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
        let addr = self.machine_st.registers[1];

        /* FIXME this is not safe */
        let block = unsafe { Fixnum::build_with_unchecked(self.machine_st.block as i64) };

        self.machine_st.unify_fixnum(block, addr);
    }

    #[inline(always)]
    pub(crate) fn get_current_scc_block(&mut self) {
        let addr = self.machine_st.registers[1];

        /* FIXME this is not safe */
        let block = unsafe { Fixnum::build_with_unchecked(self.machine_st.scc_block as i64) };

        self.machine_st.unify_fixnum(block, addr);
    }

    #[inline(always)]
    pub(crate) fn get_b_value(&mut self) {
        /* FIXME this is not safe */
        let n = unsafe { Fixnum::build_with_unchecked(i64::try_from(self.machine_st.b).unwrap()) }
            .as_cutpoint();
        self.machine_st
            .unify_fixnum(n, self.machine_st.registers[1]);
    }

    #[inline(always)]
    pub(crate) fn get_cut_point(&mut self) {
        /* FIXME this is not safe */
        let n = unsafe { Fixnum::build_with_unchecked(i64::try_from(self.machine_st.b0).unwrap()) }
            .as_cutpoint();
        self.machine_st
            .unify_fixnum(n, self.machine_st.registers[1]);
    }

    #[inline(always)]
    pub(crate) fn next_ep(&mut self) {
        let first_arg = self.deref_register(1);

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
            let e = Fixnum::build_with_checked(e).unwrap();

            machine_st.unify_fixnum(e, machine_st.registers[2]);

            if !machine_st.fail {
                let mut writer = Heap::functor_writer(functor!(atom!("dir_entry"), [fixnum(cp)]));
                let p_functor_cell =
                    step_or_resource_error!(machine_st, writer(&mut machine_st.heap));

                unify!(machine_st, p_functor_cell, machine_st.registers[3]);
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

                if and_frame.prelude.cp == 0 {
                    self.machine_st.fail = true;
                    return;
                }

                let cp = and_frame.prelude.cp - 1;
                let mut writer = Heap::functor_writer(functor!(atom!("dir_entry"), [fixnum(cp)]));

                let p_functor_cell = step_or_resource_error!(
                    self.machine_st,
                    writer(&mut self.machine_st.heap)
                );

                let e = Fixnum::build_with_checked(and_frame.prelude.e).unwrap();
                self.machine_st.unify_fixnum(e, self.machine_st.registers[2]);

                if !self.machine_st.fail {
                    unify!(self.machine_st, p_functor_cell, self.machine_st.registers[3]);
                }
            }
            _ => {
                unreachable!();
            }
        );
    }

    #[inline(always)]
    pub(crate) fn points_to_continuation_reset_marker(&mut self) {
        let addr = self.deref_register(1);

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
        let addr = self.deref_register(1);

        read_heap_cell!(addr,
            (HeapCellValueTag::Fixnum, n) => {
                let n = u32::try_from(n.get_num()).ok();
                let n = n.and_then(std::char::from_u32);

                self.machine_st.fail = match n {
                    Some(c) => non_quoted_token(once(c)),
                    None => true,
                };
            }
            /*
            (HeapCellValueTag::Char, c) => {
                self.machine_st.fail = non_quoted_token(once(c));
            }
            */
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
        match self.user_input {
            Stream::Byte(_) | Stream::Readline(_) => self.user_input.reset(),
            _ => true,
        };

        set_prompt(true);
        // let result = self.machine_st.read_term(self.user_input, &mut self.indices);
        let result = self
            .machine_st
            .read_term_from_user_input(self.user_input, &mut self.indices);
        set_prompt(false);

        match result {
            Ok(()) => Ok(()),
            Err(e) => {
                match self.user_input {
                    Stream::Byte(_) | Stream::Readline(_) => self.user_input.reset(),
                    _ => true,
                };
                Err(e)
            }
        }
    }

    #[inline(always)]
    pub(crate) fn read_term(&mut self) -> CallResult {
        set_prompt(false);

        let stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices,
            atom!("read_term"),
            3,
        )?;

        if let Stream::Readline(..) = stream {
            self.machine_st.read_term(
                stream,
                &mut self.indices,
                MachineState::read_term_from_user_input_eof_handler,
            )
        } else {
            self.machine_st.read_term(
                stream,
                &mut self.indices,
                MachineState::read_term_eof_handler,
            )
        }
    }

    #[inline(always)]
    fn read_term_and_write_to_heap(
        &mut self,
        atom_or_string: AtomOrString,
    ) -> Result<Option<TermWriteResult>, MachineStub> {
        let string = match atom_or_string {
            AtomOrString::Atom(atom!("[]")) => "".to_owned(),
            _ => atom_or_string.into(),
        };

        let chars = CharReader::new(ByteStream::from_string(string));
        let mut parser = Parser::new(chars, &mut self.machine_st);
        let op_dir = CompositeOpDir::new(&self.indices.op_dir, None);

        let term_write_result = parser
            .read_term(&op_dir, Tokens::Default)
            .map_err(|err| error_after_read_term(err, 0, &parser))
            .and_then(|term| write_term_to_heap(&term, &mut self.machine_st.heap));

        match term_write_result {
            Ok(term_write_result) => Ok(Some(term_write_result)),
            Err(CompilationError::ParserError(e)) if e.is_unexpected_eof() => {
                let value = self.machine_st.registers[2];
                self.machine_st.unify_atom(atom!("end_of_file"), value);

                Ok(None)
            }
            Err(e) => {
                let stub = functor_stub(atom!("read_term_from_chars"), 3);
                let e = self.machine_st.session_error(SessionError::from(e));

                Err(self.machine_st.error_form(e, stub))
            }
        }
    }

    #[inline(always)]
    pub(crate) fn read_from_chars(&mut self) -> CallResult {
        if let Some(atom_or_string) = self
            .machine_st
            .value_to_str_like(self.machine_st.registers[1])
        {
            if let Some(term_write_result) = self.read_term_and_write_to_heap(atom_or_string)? {
                let result = heap_loc_as_cell!(term_write_result.heap_loc);
                let var = self.deref_register(2).as_var().unwrap();

                self.machine_st.bind(var, result);
            }

            Ok(())
        } else {
            unreachable!()
        }
    }

    #[inline(always)]
    pub(crate) fn read_term_from_chars(&mut self) -> CallResult {
        if let Some(atom_or_string) = self
            .machine_st
            .value_to_str_like(self.machine_st.registers[1])
        {
            if let Some(term_write_result) = self.read_term_and_write_to_heap(atom_or_string)? {
                self.machine_st.read_term_body(term_write_result)
            } else {
                if !self.machine_st.fail {
                    // wrote end_of_file term in this case.
                    self.machine_st
                        .write_read_term_options(vec![], empty_list_as_cell!())?;
                }

                Ok(())
            }
        } else {
            unreachable!()
        }
    }

    #[inline(always)]
    pub(crate) fn reset_block(&mut self) {
        let addr = self.deref_register(1);

        read_heap_cell!(addr,
            (HeapCellValueTag::Fixnum, block) => {
                self.machine_st.block = block.get_num() as usize;
            }
            _ => {
                self.machine_st.fail = true;
            }
        );
    }

    #[inline(always)]
    pub(crate) fn reset_scc_block(&mut self) {
        let addr = self.deref_register(1);

        read_heap_cell!(addr,
            (HeapCellValueTag::Fixnum, block) => {
                self.machine_st.scc_block = block.get_num() as usize;
            }
            _ => {
                self.machine_st.fail = true;
            }
        );
    }

    #[inline(always)]
    pub(crate) fn reset_continuation_marker(&mut self) {
        let h = self.machine_st.heap.cell_len();

        self.machine_st.registers[3] = atom_as_cell!(atom!("none"));
        self.machine_st.registers[4] = heap_loc_as_cell!(h);

        step_or_resource_error!(
            self.machine_st,
            self.machine_st.heap.push_cell(heap_loc_as_cell!(h))
        );
    }

    #[inline(always)]
    pub(crate) fn set_ball(&mut self) {
        self.machine_st.set_ball();
    }

    #[inline(always)]
    pub(crate) fn set_seed(&mut self) {
        let seed = self.deref_register(1);

        match Number::try_from((seed, &self.machine_st.arena.f64_tbl)) {
            Ok(Number::Fixnum(n)) => {
                let n: u64 = Integer::from(n).try_into().unwrap();
                let rng: StdRng = SeedableRng::seed_from_u64(n);
                self.rng = rng;
            }
            Ok(Number::Integer(n)) => {
                let n: u64 = (&*n).try_into().unwrap();
                let rng: StdRng = SeedableRng::seed_from_u64(n);
                self.rng = rng;
            }
            Ok(Number::Rational(n)) => {
                if n.denominator() == &UBig::ONE {
                    let n: u64 = n.numerator().try_into().unwrap();
                    let rng: StdRng = SeedableRng::seed_from_u64(n);
                    self.rng = rng;
                }
            }
            _ => {
                self.machine_st.fail = true;
            }
        }
    }

    #[inline(always)]
    pub(crate) fn sleep(&mut self) {
        let time = self.deref_register(1);

        let time = match Number::try_from((time, &self.machine_st.arena.f64_tbl)) {
            Ok(Number::Float(n)) => n.into_inner(),
            Ok(Number::Fixnum(n)) => n.get_num() as f64,
            Ok(Number::Integer(n)) => n.to_f64().value(),
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
        let addr = self.deref_register(1);
        let port = self.deref_register(2);

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
                AtomTable::build_with(&self.machine_st.atom_tbl, &match Number::try_from((port, &self.machine_st.arena.f64_tbl)) {
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
            AtomTable::build_with(&self.machine_st.atom_tbl, &buffer)
        };

        let alias = self.machine_st.registers[4];
        let eof_action = self.machine_st.registers[5];
        let reposition = self.machine_st.registers[6];
        let stream_type = self.machine_st.registers[7];

        let options =
            self.machine_st
                .get_stream_options(alias, eof_action, reposition, stream_type);

        if options.reposition() {
            return Err(self
                .machine_st
                .reposition_error(atom!("socket_client_open"), 3));
        }

        if let Some(alias) = options.get_alias() {
            if self.indices.has_stream(alias) {
                return Err(self.machine_st.occupied_alias_permission_error(
                    alias,
                    atom!("socket_client_open"),
                    3,
                ));
            }
        }

        let stream = match TcpStream::connect(&*socket_addr.as_str()).map_err(|e| e.kind()) {
            Ok(tcp_stream) => {
                let mut stream =
                    Stream::from_tcp_stream(socket_addr, tcp_stream, &mut self.machine_st.arena);

                *stream.options_mut() = options;

                self.indices
                    .add_stream(stream, atom!("socket_client_open"), 7)
                    .map_err(|stub_gen| stub_gen(&mut self.machine_st))?;

                HeapCellValue::from(stream)
            }
            Err(ErrorKind::PermissionDenied) => {
                return Err(self.machine_st.open_permission_error(
                    addr,
                    atom!("socket_client_open"),
                    7,
                ));
            }
            Err(ErrorKind::NotFound) => {
                let stub = functor_stub(atom!("socket_client_open"), 3);
                let err = self
                    .machine_st
                    .existence_error(ExistenceError::SourceSink(addr));

                return Err(self.machine_st.error_form(err, stub));
            }
            Err(_) => {
                // for now, just fail. expand to meaningful error messages later.
                self.machine_st.fail = true;
                return Ok(());
            }
        };

        let stream_addr = self.deref_register(3);
        self.machine_st.bind(stream_addr.as_var().unwrap(), stream);

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn socket_server_open(&mut self) -> CallResult {
        let addr = self.deref_register(1);
        let socket_atom = cell_as_atom_cell!(addr).get_name();

        let socket_atom = if socket_atom == atom!("[]") {
            atom!("127.0.0.1")
        } else {
            socket_atom
        };

        let port = self.deref_register(2);

        let port = if port.is_var() {
            String::from("0")
        } else {
            match Number::try_from((port, &self.machine_st.arena.f64_tbl)) {
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

        let (tcp_listener, port): (TypedArenaPtr<TcpListener>, _) =
            match TcpListener::bind(server_addr).map_err(|e| e.kind()) {
                Ok(tcp_listener) => {
                    let port = tcp_listener.local_addr().map(|addr| addr.port()).ok();

                    if let Some(port) = port {
                        (arena_alloc!(tcp_listener, &mut self.machine_st.arena), port)
                    } else {
                        self.machine_st.fail = true;
                        return Ok(());
                    }
                }
                Err(ErrorKind::PermissionDenied) => {
                    return Err(self.machine_st.open_permission_error(
                        addr,
                        atom!("socket_server_open"),
                        2,
                    ));
                }
                _ => {
                    self.machine_st.fail = true;
                    return Ok(());
                }
            };

        let addr = self.deref_register(3);
        self.machine_st.bind(
            addr.as_var().unwrap(),
            typed_arena_ptr_as_cell!(tcp_listener),
        );

        if had_zero_port {
            self.machine_st
                .unify_fixnum(Fixnum::build_with(port), self.deref_register(2));
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn socket_server_accept(&mut self) -> CallResult {
        let alias = self.machine_st.registers[4];
        let eof_action = self.machine_st.registers[5];
        let reposition = self.machine_st.registers[6];
        let stream_type = self.machine_st.registers[7];

        let options =
            self.machine_st
                .get_stream_options(alias, eof_action, reposition, stream_type);

        if options.reposition() {
            return Err(self
                .machine_st
                .reposition_error(atom!("socket_server_accept"), 4));
        }

        if let Some(alias) = options.get_alias() {
            if self.indices.has_stream(alias) {
                return Err(self.machine_st.occupied_alias_permission_error(
                    alias,
                    atom!("socket_server_accept"),
                    4,
                ));
            }
        }

        let culprit = self.deref_register(1);

        read_heap_cell!(culprit,
            (HeapCellValueTag::Cons, cons_ptr) => {
                match_untyped_arena_ptr!(cons_ptr,
                     (ArenaHeaderTag::TcpListener, tcp_listener) => {
                         match tcp_listener.accept().ok() {
                             Some((tcp_stream, socket_addr)) => {
                                 let client = AtomTable::build_with(&self.machine_st.atom_tbl, &socket_addr.to_string());

                                 let mut tcp_stream = Stream::from_tcp_stream(
                                     client,
                                     tcp_stream,
                                     &mut self.machine_st.arena,
                                 );

                                 *tcp_stream.options_mut() = options;

                                 self.indices.add_stream(tcp_stream, atom!("socket_server_accept"), 4)
                                    .map_err(|stub_gen| {
                                        stub_gen(&mut self.machine_st)
                                    })?;

                                 let client = atom_as_cell!(client);

                                 let client_addr = self.deref_register(2);
                                 let stream_addr = self.deref_register(3);

                                 self.machine_st.bind(client_addr.as_var().unwrap(), client);
                                 self.machine_st.bind(stream_addr.as_var().unwrap(), tcp_stream.into());
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

    #[cfg(feature = "tls")]
    #[inline(always)]
    pub(crate) fn tls_client_connect(&mut self) -> CallResult {
        if let Some(hostname) = self
            .machine_st
            .value_to_str_like(self.machine_st.registers[1])
        {
            let stream0 = self.machine_st.get_stream_or_alias(
                self.machine_st.registers[2],
                &self.indices,
                atom!("tls_client_negotiate"),
                3,
            )?;

            let connector = TlsConnector::new().unwrap();
            let stream = match connector.connect(&hostname.as_str(), stream0) {
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

            self.indices
                .add_stream(stream, atom!("tls_client_negotiate"), 3)
                .map_err(|stub_gen| stub_gen(&mut self.machine_st))?;

            let stream_addr = self.deref_register(3);
            self.machine_st
                .bind(stream_addr.as_var().unwrap(), stream.into());

            Ok(())
        } else {
            unreachable!();
        }
    }

    #[cfg(feature = "tls")]
    #[inline(always)]
    pub(crate) fn tls_accept_client(&mut self) -> CallResult {
        let pkcs12 = self.string_encoding_bytes(self.machine_st.registers[1], atom!("octet"));

        if let Some(password) = self
            .machine_st
            .value_to_str_like(self.machine_st.registers[2])
        {
            let identity = match Identity::from_pkcs12(&pkcs12, &password.as_str()) {
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
                &self.indices,
                atom!("tls_server_negotiate"),
                3,
            )?;

            let acceptor = TlsAcceptor::new(identity).unwrap();

            let stream = match acceptor.accept(stream0) {
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

            self.indices
                .add_stream(stream, atom!("tls_server_negotiate"), 3)
                .map_err(|stub_gen| stub_gen(&mut self.machine_st))?;

            let stream_addr = self.deref_register(4);
            self.machine_st
                .bind(stream_addr.as_var().unwrap(), stream.into());
        } else {
            unreachable!();
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn socket_server_close(&mut self) -> CallResult {
        let culprit = self.deref_register(1);

        read_heap_cell!(culprit,
            (HeapCellValueTag::Cons, cons_ptr) => {
                match_untyped_arena_ptr!(cons_ptr,
                    (ArenaHeaderTag::TcpListener, tcp_listener) => {
                        tcp_listener.drop_payload();

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

        Err(self.machine_st.error_form(err, stub))
    }

    #[inline(always)]
    pub(crate) fn set_stream_position(&mut self) -> CallResult {
        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices,
            atom!("set_stream_position"),
            2,
        )?;

        if !stream.options().reposition() {
            let stub = functor_stub(atom!("set_stream_position"), 2);

            let err = self.machine_st.permission_error(
                Permission::Reposition,
                atom!("stream"),
                HeapCellValue::from(stream),
            );

            return Err(self.machine_st.error_form(err, stub));
        }

        let position = self.deref_register(2);

        let position = match Number::try_from((position, &self.machine_st.arena.f64_tbl)) {
            Ok(Number::Fixnum(n)) => n.get_num() as u64,
            Ok(Number::Integer(n)) => {
                let n: Result<u64, _> = (&*n).try_into();
                if let Ok(n) = n {
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
            &self.indices,
            atom!("stream_property"),
            2,
        )?;

        let atom = cell_as_atom!(self.deref_register(2));

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
            atom!("direction") => {
                atom_as_cell!(if stream.is_input_stream() && stream.is_output_stream() {
                    atom!("input_output")
                } else if stream.is_input_stream() {
                    atom!("input")
                } else {
                    atom!("output")
                })
            }
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
                    let position_term = functor!(
                        atom!("position_and_lines_read"),
                        [
                            number(position, (&mut self.machine_st.arena)),
                            number(lines_read, (&mut self.machine_st.arena))
                        ]
                    );

                    let mut functor_writer = Heap::functor_writer(position_term);

                    resource_error_call_result!(
                        self.machine_st,
                        functor_writer(&mut self.machine_st.heap)
                    )
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
            atom!("reposition") => atom_as_cell!(if stream.options().reposition() {
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
        let key = cell_as_atom!(self.deref_register(1));

        let value = self.machine_st.registers[2];
        let mut ball = Ball::new();

        ball.boundary = self.machine_st.heap.cell_len();
        ball.pstr_boundary = step_or_resource_error!(
            self.machine_st,
            copy_term(
                CopyBallTerm::new(
                    &mut self.machine_st.attr_var_init.attr_var_queue,
                    &mut self.machine_st.stack,
                    &mut self.machine_st.heap,
                    &mut ball.stub,
                ),
                value,
                AttrVarPolicy::DeepCopy,
            )
        );

        self.indices.global_variables.insert(key, (ball, None));
    }

    #[inline(always)]
    pub(crate) fn store_backtrackable_global_var(&mut self) {
        let key = cell_as_atom!(self.deref_register(1));
        let new_value = self.deref_register(2);

        match self.indices.global_variables.get_mut(&key) {
            Some((_, ref mut loc)) => match loc {
                Some(ref mut value) => {
                    self.machine_st
                        .trail(TrailRef::BlackboardOffset(key, *value));
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
            let a2 = self.deref_register(2);
            self.machine_st.unify_atom(atom!("[]"), a2);

            return;
        }

        let seen_vars = self
            .machine_st
            .attr_vars_of_term(self.machine_st.registers[1]);

        let outcome = step_or_resource_error!(
            self.machine_st,
            sized_iter_to_heap_list(
                &mut self.machine_st.heap,
                seen_vars.len(),
                seen_vars.into_iter(),
            )
        );

        unify_fn!(self.machine_st, self.machine_st.registers[2], outcome);
    }

    #[inline(always)]
    pub(crate) fn term_variables(&mut self) {
        let stored_v = self.deref_register(1);
        let a2 = self.deref_register(2);

        if stored_v.is_constant() {
            self.machine_st.unify_atom(atom!("[]"), a2);
            return;
        }

        let stored_v = if stored_v.is_stack_var() {
            let h = self.machine_st.heap.cell_len();

            step_or_resource_error!(
                self.machine_st,
                self.machine_st.heap.push_cell(heap_loc_as_cell!(h))
            );

            self.machine_st.bind(Ref::heap_cell(h), stored_v);
            heap_loc_as_cell!(h)
        } else {
            stored_v
        };

        let mut seen_set = IndexSet::with_hasher(FxBuildHasher::default());
        self.machine_st.variable_set(&mut seen_set, stored_v);

        let outcome = step_or_resource_error!(
            self.machine_st,
            sized_iter_to_heap_list(
                &mut self.machine_st.heap,
                seen_set.len(),
                seen_set.into_iter(),
            )
        );

        unify_fn!(self.machine_st, a2, outcome);
    }

    #[inline(always)]
    pub(crate) fn term_variables_under_max_depth(&mut self) {
        // Term, MaxDepth, VarList
        let max_depth =
            unsafe { self.deref_register(2).to_fixnum_or_cut_point_unchecked() }.get_num() as usize;

        self.machine_st.term_variables_under_max_depth(
            self.machine_st.registers[1],
            max_depth,
            self.machine_st.registers[3],
        );
    }

    #[inline(always)]
    pub(crate) fn truncate_lifted_heap_to(&mut self) {
        let a1 = self.deref_register(1);
        let lh_offset = unsafe { a1.to_fixnum_or_cut_point_unchecked() }.get_num() as usize;

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

    fn walk_code_at_ptr(&mut self, index_ptr: usize) -> Result<HeapCellValue, usize> {
        let orig_h = self.machine_st.heap.cell_len();
        let mut h = orig_h;

        let mut functors = vec![];
        let mut functor_list = vec![];

        walk_code(&self.code, index_ptr, |instr| {
            let old_len = functors.len();
            instr.enqueue_functors(&mut self.machine_st.arena, &mut functors);

            for functor in &functors[old_len..] {
                let functor_len = functor.len();

                match functor_len {
                    0 => {}
                    1 => {
                        functor_list.push(heap_loc_as_cell!(h));
                        h += cell_index!(Heap::compute_functor_byte_size(functor));
                    }
                    _ => {
                        functor_list.push(str_loc_as_cell!(h));
                        h += cell_index!(Heap::compute_functor_byte_size(functor));
                    }
                };
            }
        });

        let mut writer = self.machine_st.heap.reserve(h - orig_h)?;

        writer.write_with(|section| {
            for functor in functors {
                let mut functor_writer = ReservedHeapSection::functor_writer(functor);
                functor_writer(section);
            }
        });

        sized_iter_to_heap_list(
            &mut self.machine_st.heap,
            functor_list.len(),
            functor_list.into_iter(),
        )
    }

    #[inline(always)]
    pub(crate) fn wam_instructions(&mut self) -> CallResult {
        let module_name = cell_as_atom!(self.deref_register(1));
        let name = cell_as_atom!(self.deref_register(2));
        let arity = self.deref_register(3);

        let arity = match Number::try_from((arity, &self.machine_st.arena.f64_tbl)) {
            Ok(Number::Fixnum(n)) => n.get_num() as usize,
            Ok(Number::Integer(n)) => {
                let value: usize = (&*n).try_into().unwrap();
                value
            }
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
                    let err = self.machine_st.session_error(SessionError::from(
                        CompilationError::InvalidModuleResolution(module_name),
                    ));

                    return Err(self.machine_st.error_form(err, stub));
                }
            },
        };

        let first_idx = first_idx.and_then(|first_idx| {
            self.machine_st
                .arena
                .code_index_tbl
                .get_entry(first_idx.into())
                .local()
        });

        let first_idx = if let Some(idx) = first_idx {
            idx
        } else {
            let stub = functor_stub(name, arity);
            let err = self
                .machine_st
                .existence_error(ExistenceError::Procedure(name, arity));

            return Err(self.machine_st.error_form(err, stub));
        };

        let listing =
            resource_error_call_result!(self.machine_st, self.walk_code_at_ptr(first_idx));

        let listing_var = self.machine_st.registers[4];

        unify!(self.machine_st, listing, listing_var);
        Ok(())
    }

    #[inline(always)]
    pub(crate) fn inlined_instructions(&mut self) {
        let index_ptr = self.deref_register(1);
        let index_ptr = match Number::try_from((index_ptr, &self.machine_st.arena.f64_tbl)) {
            Ok(Number::Fixnum(n)) => n.get_num() as usize,
            Ok(Number::Integer(n)) => {
                let value: usize = (&*n).try_into().unwrap();
                value
            }
            _ => {
                unreachable!()
            }
        };

        let listing = step_or_resource_error!(self.machine_st, self.walk_code_at_ptr(index_ptr));

        let listing_var = self.machine_st.registers[2];

        unify!(self.machine_st, listing, listing_var);
    }

    #[inline(always)]
    pub(crate) fn write_term(&mut self) -> CallResult {
        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices,
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
                let err = self
                    .machine_st
                    .existence_error(ExistenceError::Stream(self.machine_st.registers[1]));

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
        let chars = resource_error_call_result!(
            self.machine_st,
            self.machine_st.heap.allocate_cstr(&result)
        );

        let result_addr = self.deref_register(1);
        let var = result_addr.as_var().unwrap();

        self.machine_st.bind(var, chars);

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn scryer_prolog_version(&mut self) {
        use git_version::git_version;

        let buffer = git_version!(cargo_prefix = "cargo:", fallback = "unknown");
        let cstr_cell =
            step_or_resource_error!(self.machine_st, self.machine_st.heap.allocate_cstr(buffer));

        unify!(self.machine_st, cstr_cell, self.machine_st.registers[1]);
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

        let byte = Fixnum::build_with(bytes[0]);
        self.machine_st.unify_fixnum(byte, arg);
    }

    #[inline(always)]
    pub(crate) fn crypto_data_hash(&mut self) {
        let encoding = cell_as_atom!(self.deref_register(2));
        let bytes = self.string_encoding_bytes(self.machine_st.registers[1], encoding);

        let algorithm = cell_as_atom!(self.deref_register(4));

        let ints_list = match algorithm {
            atom!("sha3_224") => {
                let mut context = Sha3_224::new();
                context.update(&bytes);

                let finalized_context = context.finalize();
                let context_len = finalized_context.len();

                step_or_resource_error!(
                    self.machine_st,
                    sized_iter_to_heap_list(
                        &mut self.machine_st.heap,
                        context_len,
                        finalized_context
                            .iter()
                            .map(|b| fixnum_as_cell!(Fixnum::build_with(*b)))
                    )
                )
            }
            atom!("sha3_256") => {
                let mut context = Sha3_256::new();
                context.update(&bytes);
                let finalized_context = context.finalize();
                let context_len = finalized_context.len();

                step_or_resource_error!(
                    self.machine_st,
                    sized_iter_to_heap_list(
                        &mut self.machine_st.heap,
                        context_len,
                        finalized_context
                            .iter()
                            .map(|b| fixnum_as_cell!(Fixnum::build_with(*b)))
                    )
                )
            }
            atom!("sha3_384") => {
                let mut context = Sha3_384::new();
                context.update(&bytes);
                let finalized_context = context.finalize();
                let context_len = finalized_context.len();

                step_or_resource_error!(
                    self.machine_st,
                    sized_iter_to_heap_list(
                        &mut self.machine_st.heap,
                        context_len,
                        finalized_context
                            .iter()
                            .map(|b| fixnum_as_cell!(Fixnum::build_with(*b)))
                    )
                )
            }
            atom!("sha3_512") => {
                let mut context = Sha3_512::new();
                context.update(&bytes);
                let finalized_context = context.finalize();
                let context_len = finalized_context.len();

                step_or_resource_error!(
                    self.machine_st,
                    sized_iter_to_heap_list(
                        &mut self.machine_st.heap,
                        context_len,
                        finalized_context
                            .iter()
                            .map(|b| fixnum_as_cell!(Fixnum::build_with(*b))),
                    )
                )
            }
            atom!("blake2s256") => {
                let mut context = Blake2s256::new();
                context.update(&bytes);
                let finalized_context = context.finalize();
                let context_len = finalized_context.len();

                step_or_resource_error!(
                    self.machine_st,
                    sized_iter_to_heap_list(
                        &mut self.machine_st.heap,
                        context_len,
                        finalized_context
                            .iter()
                            .map(|b| fixnum_as_cell!(Fixnum::build_with(*b))),
                    )
                )
            }
            atom!("blake2b512") => {
                let mut context = Blake2b512::new();
                context.update(&bytes);
                let finalized_context = context.finalize();
                let context_len = finalized_context.len();

                step_or_resource_error!(
                    self.machine_st,
                    sized_iter_to_heap_list(
                        &mut self.machine_st.heap,
                        context_len,
                        finalized_context
                            .iter()
                            .map(|b| fixnum_as_cell!(Fixnum::build_with(*b))),
                    )
                )
            }
            atom!("ripemd160") => {
                let mut context = Ripemd160::new();
                context.update(&bytes);
                let finalized_context = context.finalize();
                let context_len = finalized_context.len();

                step_or_resource_error!(
                    self.machine_st,
                    sized_iter_to_heap_list(
                        &mut self.machine_st.heap,
                        context_len,
                        finalized_context
                            .iter()
                            .map(|b| fixnum_as_cell!(Fixnum::build_with(*b)))
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

                step_or_resource_error!(
                    self.machine_st,
                    sized_iter_to_heap_list(
                        &mut self.machine_st.heap,
                        ints.as_ref().len(),
                        ints.as_ref()
                            .iter()
                            .map(|b| fixnum_as_cell!(Fixnum::build_with(*b)))
                    )
                )
            }
        };

        unify!(self.machine_st, self.machine_st.registers[3], ints_list);
    }

    #[inline(always)]
    pub(crate) fn crypto_hmac(&mut self) {
        let encoding = cell_as_atom!(self.deref_register(2));
        let data = self.string_encoding_bytes(self.machine_st.registers[1], encoding);

        let stub_gen = || functor_stub(atom!("crypto_data_hash"), 3);

        let key = self
            .machine_st
            .integers_to_bytevec(self.machine_st.registers[3], stub_gen);

        let algorithm = cell_as_atom!(self.deref_register(5));
        let ralg = match algorithm {
            atom!("sha256") => hmac::HMAC_SHA256,
            atom!("sha384") => hmac::HMAC_SHA384,
            atom!("sha512") => hmac::HMAC_SHA512,
            _ => {
                unreachable!()
            }
        };

        let rkey = hmac::Key::new(ralg, key.as_ref());
        let tag = hmac::sign(&rkey, &data);

        let ints_list = step_or_resource_error!(
            self.machine_st,
            sized_iter_to_heap_list(
                &mut self.machine_st.heap,
                tag.as_ref().len(),
                tag.as_ref()
                    .iter()
                    .map(|b| fixnum_as_cell!(Fixnum::build_with(*b)))
            )
        );

        unify!(self.machine_st, self.machine_st.registers[4], ints_list);
    }

    #[inline(always)]
    pub(crate) fn crypto_data_hkdf(&mut self) {
        let encoding = cell_as_atom!(self.deref_register(2));
        let data = self.string_encoding_bytes(self.machine_st.registers[1], encoding);

        let stub1_gen = || functor_stub(atom!("crypto_data_hkdf"), 4);
        let salt = self
            .machine_st
            .integers_to_bytevec(self.machine_st.registers[3], stub1_gen);

        let stub2_gen = || functor_stub(atom!("crypto_data_hkdf"), 4);
        let info = self
            .machine_st
            .integers_to_bytevec(self.machine_st.registers[4], stub2_gen);

        let algorithm = cell_as_atom!(self.deref_register(5));

        let length = self.deref_register(6);

        let length = match Number::try_from((length, &self.machine_st.arena.f64_tbl)) {
            Ok(Number::Fixnum(n)) => usize::try_from(n.get_num()).unwrap(),
            Ok(Number::Integer(n)) => match (&*n).try_into() as Result<usize, _> {
                Ok(u) => u,
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
            let mut bytes: Vec<u8> = vec![0; length];

            match salt.extract(&data).expand(&[&info[..]], MyKey(length)) {
                Ok(r) => {
                    r.fill(&mut bytes).unwrap();
                }
                _ => {
                    self.machine_st.fail = true;
                    return;
                }
            }

            step_or_resource_error!(
                self.machine_st,
                sized_iter_to_heap_list(
                    &mut self.machine_st.heap,
                    bytes.len(),
                    bytes
                        .iter()
                        .map(|b| fixnum_as_cell!(Fixnum::build_with(*b)))
                )
            )
        };

        unify!(self.machine_st, self.machine_st.registers[7], ints_list);
    }

    #[inline(always)]
    pub(crate) fn crypto_password_hash(&mut self) {
        let stub1_gen = || functor_stub(atom!("crypto_password_hash"), 3);
        let data = self
            .machine_st
            .integers_to_bytevec(self.machine_st.registers[1], stub1_gen);
        let stub2_gen = || functor_stub(atom!("crypto_password_hash"), 3);
        let salt = self
            .machine_st
            .integers_to_bytevec(self.machine_st.registers[2], stub2_gen);

        let iterations = self.deref_register(3);

        let iterations = match Number::try_from((iterations, &self.machine_st.arena.f64_tbl)) {
            Ok(Number::Fixnum(n)) => u64::try_from(n.get_num()).unwrap(),
            Ok(Number::Integer(n)) => {
                let n: Result<u64, _> = (&*n).try_into();
                match n {
                    Ok(i) => i,
                    _ => {
                        self.machine_st.fail = true;
                        return;
                    }
                }
            }
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

            step_or_resource_error!(
                self.machine_st,
                sized_iter_to_heap_list(
                    &mut self.machine_st.heap,
                    bytes.len(),
                    bytes
                        .iter()
                        .map(|b| fixnum_as_cell!(Fixnum::build_with(*b)))
                )
            )
        };

        unify!(self.machine_st, self.machine_st.registers[4], ints_list);
    }

    #[cfg(feature = "crypto-full")]
    #[inline(always)]
    pub(crate) fn crypto_data_encrypt(&mut self) {
        let encoding = cell_as_atom!(self.deref_register(3));

        let data = self.string_encoding_bytes(self.machine_st.registers[1], encoding);
        let aad = self.string_encoding_bytes(self.machine_st.registers[2], encoding);

        let stub2_gen = || functor_stub(atom!("crypto_data_encrypt"), 7);
        let key = self
            .machine_st
            .integers_to_bytevec(self.machine_st.registers[4], stub2_gen);

        let stub3_gen = || functor_stub(atom!("crypto_data_encrypt"), 7);
        let iv = self
            .machine_st
            .integers_to_bytevec(self.machine_st.registers[5], stub3_gen);

        let unbound_key = aead::UnboundKey::new(&aead::CHACHA20_POLY1305, &key).unwrap();
        let nonce = aead::Nonce::try_assume_unique_for_key(&iv).unwrap();
        let key = aead::LessSafeKey::new(unbound_key);

        let mut in_out = data;

        let tag = match key.seal_in_place_separate_tag(nonce, aead::Aad::from(aad), &mut in_out) {
            Ok(d) => d,
            _ => {
                self.machine_st.fail = true;
                return;
            }
        };

        let tag_list = step_or_resource_error!(
            self.machine_st,
            sized_iter_to_heap_list(
                &mut self.machine_st.heap,
                tag.as_ref().len(),
                tag.as_ref()
                    .iter()
                    .map(|b| fixnum_as_cell!(Fixnum::build_with(*b)))
            )
        );

        let complete_string = step_or_resource_error!(self.machine_st, self.u8s_to_string(&in_out));

        unify!(self.machine_st, self.machine_st.registers[6], tag_list);
        unify!(
            self.machine_st,
            self.machine_st.registers[7],
            complete_string
        );
    }

    #[cfg(feature = "crypto-full")]
    #[inline(always)]
    pub(crate) fn crypto_data_decrypt(&mut self) {
        let data = self.string_encoding_bytes(self.machine_st.registers[1], atom!("octet"));
        let encoding = cell_as_atom!(self.deref_register(5));

        let aad = self.string_encoding_bytes(self.machine_st.registers[2], encoding);
        let stub1_gen = || functor_stub(atom!("crypto_data_decrypt"), 7);

        let key = self
            .machine_st
            .integers_to_bytevec(self.machine_st.registers[3], stub1_gen);
        let stub2_gen = || functor_stub(atom!("crypto_data_decrypt"), 7);
        let iv = self
            .machine_st
            .integers_to_bytevec(self.machine_st.registers[4], stub2_gen);

        let unbound_key = aead::UnboundKey::new(&aead::CHACHA20_POLY1305, &key).unwrap();
        let nonce = aead::Nonce::try_assume_unique_for_key(&iv).unwrap();
        let key = aead::LessSafeKey::new(unbound_key);

        let mut in_out = data;

        let complete_string = {
            let decrypted_data = match key.open_in_place(nonce, aead::Aad::from(aad), &mut in_out) {
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

            if buffer.is_empty() {
                empty_list_as_cell!()
            } else {
                step_or_resource_error!(
                    self.machine_st,
                    self.machine_st.heap.allocate_cstr(&buffer)
                )
            }
        };

        unify!(
            self.machine_st,
            self.machine_st.registers[6],
            complete_string
        );
    }

    #[inline(always)]
    pub(crate) fn crypto_curve_scalar_mult(&mut self) {
        let stub_gen = || functor_stub(atom!("crypto_curve_scalar_mult"), 4);
        let scalar_bytes = self
            .machine_st
            .integers_to_bytevec(self.machine_st.registers[2], stub_gen);
        let point_bytes = self
            .machine_st
            .integers_to_bytevec(self.machine_st.registers[3], stub_gen);

        let mut point = secp256k1::Point::decode(&point_bytes).unwrap();
        let scalar = secp256k1::Scalar::decode_reduce(&scalar_bytes);
        point *= scalar;

        let uncompressed = step_or_resource_error!(
            self.machine_st,
            self.u8s_to_string(&point.encode_uncompressed())
        );

        unify!(self.machine_st, self.machine_st.registers[4], uncompressed);
    }

    #[inline(always)]
    pub(crate) fn ed25519_seed_to_public_key(&mut self) {
        let stub_gen = || functor_stub(atom!("ed25519_seed_keypair"), 2);
        let seed_bytes = self
            .machine_st
            .integers_to_bytevec(self.machine_st.registers[1], stub_gen);

        let skey = ed25519::PrivateKey::from_seed(&seed_bytes);

        let complete_string = step_or_resource_error!(
            self.machine_st,
            self.u8s_to_string(skey.public_key.encoded.as_ref())
        );

        unify!(
            self.machine_st,
            self.machine_st.registers[2],
            complete_string
        );
    }

    #[inline(always)]
    pub(crate) fn ed25519_sign_raw(&mut self) {
        let stub_gen = || functor_stub(atom!("ed25519_sign"), 4);
        let seed_bytes = self
            .machine_st
            .integers_to_bytevec(self.machine_st.registers[1], stub_gen);

        let skey = ed25519::PrivateKey::from_seed(&seed_bytes);

        let encoding = cell_as_atom!(self.deref_register(3));
        let data = self.string_encoding_bytes(self.machine_st.registers[2], encoding);

        let sig = skey.sign_raw(&data);
        let sig_list = step_or_resource_error!(
            self.machine_st,
            sized_iter_to_heap_list(
                &mut self.machine_st.heap,
                sig.as_ref().len(),
                sig.as_ref()
                    .iter()
                    .map(|b| fixnum_as_cell!(Fixnum::build_with(*b)))
            )
        );

        unify!(self.machine_st, self.machine_st.registers[4], sig_list);
    }

    #[inline(always)]
    pub(crate) fn ed25519_verify_raw(&mut self) {
        let key_bytes = self.string_encoding_bytes(self.machine_st.registers[1], atom!("octet"));
        let pkey = ed25519::PublicKey::decode(&key_bytes).unwrap();

        let encoding = cell_as_atom!(self.deref_register(3));
        let data = self.string_encoding_bytes(self.machine_st.registers[2], encoding);

        let stub_gen = || functor_stub(atom!("ed25519_verify"), 4);

        let signature = self
            .machine_st
            .integers_to_bytevec(self.machine_st.registers[4], stub_gen);

        self.machine_st.fail = !pkey.verify_raw(&signature, &data);
    }

    #[inline(always)]
    pub(crate) fn curve25519_scalar_mult(&mut self) {
        let stub1_gen = || functor_stub(atom!("curve25519_scalar_mult"), 3);
        let scalar_bytes = self
            .machine_st
            .integers_to_bytevec(self.machine_st.registers[1], stub1_gen);
        let stub2_gen = || functor_stub(atom!("curve25519_scalar_mult"), 3);
        let point_bytes = self
            .machine_st
            .integers_to_bytevec(self.machine_st.registers[2], stub2_gen);

        let result = x25519::x25519(
            &<[u8; 32]>::try_from(&point_bytes[..]).unwrap(),
            &<[u8; 32]>::try_from(&scalar_bytes[..]).unwrap(),
        );

        let string = step_or_resource_error!(self.machine_st, self.u8s_to_string(&result[..]));

        unify!(self.machine_st, self.machine_st.registers[3], string);
    }

    #[inline(always)]
    pub(crate) fn first_non_octet(&mut self) {
        let addr = self.deref_register(1);

        if let Some(string) = self.machine_st.value_to_str_like(addr) {
            for c in string.as_str().chars() {
                if c as u32 > 255 {
                    let non_octet =
                        AtomTable::build_with(&self.machine_st.atom_tbl, &c.to_string());
                    self.machine_st
                        .unify_atom(non_octet, self.machine_st.registers[2]);
                    return;
                }
            }
        }

        self.machine_st.fail = true;
    }

    #[inline(always)]
    pub(crate) fn load_html(&mut self) -> Result<(), usize> {
        if let Some(string) = self
            .machine_st
            .value_to_str_like(self.machine_st.registers[1])
        {
            let document = scraper::Html::parse_document(&string.as_str());

            let root_nodes = document
                .tree
                .root()
                .children()
                .map(|child| self.html_node_to_term(child))
                .collect::<Result<Vec<_>, _>>()?;

            let nodes = sized_iter_to_heap_list(
                &mut self.machine_st.heap,
                root_nodes.len(),
                root_nodes.into_iter(),
            )?;

            unify!(self.machine_st, self.machine_st.registers[2], nodes);
        } else {
            self.machine_st.fail = true;
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn load_xml(&mut self) -> Result<(), usize> {
        if let Some(string) = self
            .machine_st
            .value_to_str_like(self.machine_st.registers[1])
        {
            match roxmltree::Document::parse(&string.as_str()) {
                Ok(doc) => {
                    let result = self.xml_node_to_term(doc.root_element())?;
                    unify!(self.machine_st, self.machine_st.registers[2], result);
                }
                _ => {
                    self.machine_st.fail = true;
                }
            }
        } else {
            self.machine_st.fail = true;
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn get_env(&mut self) {
        if let Some(key) = self
            .machine_st
            .value_to_str_like(self.machine_st.registers[1])
        {
            match env::var(&*key.as_str()) {
                Ok(value) => {
                    let cstr = step_or_resource_error!(
                        self.machine_st,
                        self.machine_st.heap.allocate_cstr(&value)
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
        let key = self
            .machine_st
            .value_to_str_like(self.machine_st.registers[1])
            .unwrap();
        let value = self
            .machine_st
            .value_to_str_like(self.machine_st.registers[2])
            .unwrap();

        env::set_var(&*key.as_str(), &*value.as_str());
    }

    #[inline(always)]
    pub(crate) fn unset_env(&mut self) {
        let key = self
            .machine_st
            .value_to_str_like(self.machine_st.registers[1])
            .unwrap();
        env::remove_var(&*key.as_str());
    }

    #[inline(always)]
    pub(crate) fn pid(&mut self) {
        let pid = process::id();

        match fixnum!(Number, pid as i64, &mut self.machine_st.arena) {
            Number::Fixnum(pid) => {
                self.machine_st
                    .unify_fixnum(pid, self.machine_st.registers[1]);
            }
            Number::Integer(pid) => {
                self.machine_st
                    .unify_big_int(pid, self.machine_st.registers[1]);
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
        fn command_result(
            machine: &mut MachineState,
            command: std::io::Result<process::ExitStatus>,
        ) {
            match command {
                Ok(status) => match status.code() {
                    Some(code) => {
                        let code = integer_as_cell!(Number::arena_from(code, &mut machine.arena));
                        unify!(machine, code, machine.registers[2]);
                    }
                    _ => {
                        machine.fail = true;
                    }
                },
                _ => {
                    machine.fail = true;
                }
            }
        }

        let a1 = self.deref_register(1);
        let command = self.machine_st.value_to_str_like(a1).unwrap();

        match env::var("SHELL") {
            Ok(value) => {
                let command = process::Command::new(value)
                    .arg("-c")
                    .arg(&*command.as_str())
                    .status();
                command_result(&mut self.machine_st, command);
            }
            _ => match env::var("COMSPEC") {
                Ok(value) => {
                    let command = process::Command::new(value)
                        .arg("/C")
                        .arg(&*command.as_str())
                        .status();
                    command_result(&mut self.machine_st, command);
                }
                _ => {
                    self.machine_st.fail = true;
                }
            },
        };
    }

    pub(crate) fn process_create(&mut self) -> CallResult {
        fn stub_gen() -> Vec<FunctorElement> {
            functor_stub(atom!("process_create"), 3)
        }

        // String
        let exe_r = self.deref_register(1);
        // [String,...]
        let args_r = self.deref_register(2);
        // [std] | [null] | [pipe, Var] | [file, String]
        let stdin_r = self.deref_register(3);
        let stdout_r = self.deref_register(4);
        let stderr_r = self.deref_register(5);
        // [env | environment, [[String, String],...]]
        let env_r = self.deref_register(6);
        // String ("." for keep current cwd)
        let cwd_r = self.deref_register(7);
        // Var
        let pid_r = self.deref_register(8);

        let exe = self
            .machine_st
            .value_to_str_like(exe_r)
            .expect("invalid values should have been rejected on the prolog side");

        let args = self
            .machine_st
            .try_from_list(args_r, stub_gen)
            .expect("invalid values should have been rejected on the prolog side")
            .into_iter()
            .map(|arg| {
                self.machine_st
                    .value_to_str_like(arg)
                    .expect("invalid values should have been rejected on the prolog side")
                    .as_str()
                    .to_string()
            })
            .collect::<Vec<_>>();

        let stdin_args = self.machine_st.try_from_list(stdin_r, stub_gen)?;
        let stdin = self.handle_input_stream(&stdin_args)?;

        let stdout_args = self.machine_st.try_from_list(stdout_r, stub_gen)?;
        let stdout = self.handle_output_stream(&stdout_args)?;

        let stderr_args = self.machine_st.try_from_list(stderr_r, stub_gen)?;
        let stderr = self.handle_output_stream(&stderr_args)?;

        let env_args = self.machine_st.try_from_list(env_r, stub_gen)?;

        let clear_env = match env_args[0].to_atom() {
            Some(atom!("env")) => true,
            Some(atom!("environment")) => false,
            _ => panic!("Invalid value for clear_env"),
        };

        let envs = self
            .machine_st
            .try_from_list(env_args[1], stub_gen)?
            .into_iter()
            .map(|entry| {
                let entry = self.machine_st.try_from_list(entry, stub_gen)?;
                let name = self
                    .machine_st
                    .value_to_str_like(entry[0])
                    .expect("invalid values should have been rejected on the prolog side")
                    .as_str()
                    .to_string();
                let value = self
                    .machine_st
                    .value_to_str_like(entry[1])
                    .expect("invalid values should have been rejected on the prolog side")
                    .as_str()
                    .to_string();
                Ok((name, value))
            })
            .collect::<Result<Vec<_>, MachineStub>>()?;

        let cwd = self
            .machine_st
            .value_to_str_like(cwd_r)
            .expect("invalid values should have been rejected on the prolog side");

        let mut command = std::process::Command::new(&*exe.as_str());
        command.args(args);

        if &*cwd.as_str() != "." {
            command.current_dir(&*cwd.as_str());
        }

        if clear_env {
            command.env_clear();
        }

        command
            .envs(envs)
            .stdin(stdin)
            .stdout(stdout)
            .stderr(stderr);

        match command.spawn() {
            #[cfg_attr(rust_version = "1.87.0", expect(unused_mut))]
            Ok(mut child) => {
                #[cfg(not(rust_version = "1.87.0"))]
                {
                    self.anon_pipe_compat(&mut child, &stdin_args, &stdout_args, &stderr_args)?;
                }

                let child_process_alloc: TypedArenaPtr<Child> =
                    arena_alloc!(child, &mut self.machine_st.arena);

                unify!(
                    self.machine_st,
                    pid_r,
                    typed_arena_ptr_as_cell!(child_process_alloc)
                );

                Ok(())
            }
            Err(_) => {
                let perm_error = self.machine_st.permission_error(
                    Permission::Create,
                    atom!("process"),
                    stub_gen(),
                );
                Err(self.machine_st.error_form(perm_error, stub_gen()))
            }
        }
    }

    #[cfg(not(rust_version = "1.87.0"))]
    fn anon_pipe_compat(
        &mut self,
        child: &mut std::process::Child,
        stdin_args: &[HeapCellValue],
        stdout_args: &[HeapCellValue],
        stderr_args: &[HeapCellValue],
    ) -> CallResult {
        if let Some(atom!("pipe")) = stdin_args[0].to_atom() {
            let writer = child.stdin.take().expect("Should have captured stdin");

            let stream = Stream::from_pipe_writer(writer, &mut self.machine_st.arena);

            self.indices
                .add_stream(stream, atom!("process_create"), 3)
                .map_err(|stub_gen| stub_gen(&mut self.machine_st))?;

            unify!(self.machine_st, stdin_args[1], HeapCellValue::from(stream));
        }

        if let Some(atom!("pipe")) = stdout_args[0].to_atom() {
            let writer = child.stdout.take().expect("Should have captured stdout");

            let stream = Stream::from_pipe_reader(
                PipeReader(PipeReaderInner::Stdout(writer)),
                &mut self.machine_st.arena,
            );

            self.indices
                .add_stream(stream, atom!("process_create"), 3)
                .map_err(|stub_gen| stub_gen(&mut self.machine_st))?;

            unify!(self.machine_st, stdout_args[1], HeapCellValue::from(stream));
        }

        if let Some(atom!("pipe")) = stderr_args[0].to_atom() {
            let writer = child.stderr.take().expect("Should have captured stderr");

            let stream = Stream::from_pipe_reader(
                PipeReader(PipeReaderInner::Stderr(writer)),
                &mut self.machine_st.arena,
            );

            self.indices
                .add_stream(stream, atom!("process_create"), 3)
                .map_err(|stub_gen| stub_gen(&mut self.machine_st))?;

            unify!(self.machine_st, stderr_args[1], HeapCellValue::from(stream));
        }

        Ok(())
    }

    fn handle_output_stream(&mut self, args: &[HeapCellValue]) -> Result<Stdio, MachineStub> {
        Ok(match args[0].to_atom() {
            Some(atom!("std")) => Stdio::inherit(),
            Some(atom!("null")) => Stdio::null(),
            Some(atom!("pipe")) => {
                #[cfg(rust_version = "1.87.0")]
                #[allow(clippy::incompatible_msrv)]
                {
                    let (reader, writer) = match std::io::pipe() {
                        Ok(pipe_pair) => pipe_pair,
                        Err(_) => {
                            return Err(self.machine_st.open_permission_error(
                                atom!("anonymous_pipe"),
                                atom!("process_create"),
                                3,
                            ));
                        }
                    };

                    let stream = Stream::from_pipe_reader(reader, &mut self.machine_st.arena);

                    self.indices
                        .add_stream(stream, atom!("process_create"), 3)
                        .map_err(|stub_gen| stub_gen(&mut self.machine_st))?;

                    self.machine_st
                        .bind(args[1].as_var().unwrap(), stream.into());

                    Stdio::from(writer)
                }

                #[cfg(not(rust_version = "1.87.0"))]
                {
                    Stdio::piped()
                }
            }
            Some(atom!("file")) => {
                let path = self.machine_st.value_to_str_like(args[1]).unwrap();

                let file = match std::fs::File::open(&*path.as_str()) {
                    Ok(file) => file,
                    Err(_) => {
                        return Err(self.machine_st.open_permission_error(
                            args[1],
                            atom!("process_create"),
                            3,
                        ));
                    }
                };
                Stdio::from(file)
            }
            _ => {
                panic!("Invalid stdout tag")
            }
        })
    }

    fn handle_input_stream(&mut self, args: &[HeapCellValue]) -> Result<Stdio, MachineStub> {
        Ok(match args[0].to_atom() {
            Some(atom!("std")) => Stdio::inherit(),
            Some(atom!("null")) => Stdio::null(),
            Some(atom!("pipe")) => {
                #[cfg(rust_version = "1.87.0")]
                #[allow(clippy::incompatible_msrv)]
                {
                    let (reader, writer) = match std::io::pipe() {
                        Ok(pipe_pair) => pipe_pair,
                        Err(_) => {
                            return Err(self.machine_st.open_permission_error(
                                atom!("anonymous_pipe"),
                                atom!("process_create"),
                                3,
                            ));
                        }
                    };

                    let stream = Stream::from_pipe_writer(writer, &mut self.machine_st.arena);

                    self.indices
                        .add_stream(stream, atom!("process_create"), 3)
                        .map_err(|stub_gen| stub_gen(&mut self.machine_st))?;

                    self.machine_st
                        .bind(args[1].as_var().unwrap(), stream.into());

                    Stdio::from(reader)
                }

                #[cfg(not(rust_version = "1.87.0"))]
                {
                    Stdio::piped()
                }
            }
            Some(atom!("file")) => {
                let path = self.machine_st.value_to_str_like(args[1]).unwrap();

                let file = match std::fs::File::open(&*path.as_str()) {
                    Ok(file) => file,
                    Err(_) => {
                        return Err(self.machine_st.open_permission_error(
                            args[1],
                            atom!("process_create"),
                            3,
                        ));
                    }
                };
                Stdio::from(file)
            }
            _ => {
                panic!("Invalid stdin tag")
            }
        })
    }

    pub(crate) fn process_id(&mut self) -> CallResult {
        fn stub_gen() -> Vec<FunctorElement> {
            functor_stub(atom!("process_id"), 2)
        }

        // Process
        let process_r = self.deref_register(1);
        // Pid
        let pid_r = self.deref_register(2);

        let Some(ptr) = process_r.to_untyped_arena_ptr() else {
            let err = self.machine_st.type_error(ValidType::Process, process_r);
            return Err(self.machine_st.error_form(err, stub_gen()));
        };

        let process = match_untyped_arena_ptr!(ptr,
            (ArenaHeaderTag::ChildProcess, child_process) => {
                child_process
            }
            (ArenaHeaderTag::Dropped, _dropped) => {
                let err = self.machine_st.existence_error(ExistenceError::Process(process_r));
                return Err(self.machine_st.error_form(err, stub_gen()));
            }
            _ => {
                let err = self.machine_st.type_error(ValidType::Process, process_r);
                return Err(self.machine_st.error_form(err, stub_gen()));
            }
        );

        self.machine_st.bind(
            pid_r.as_var().unwrap(),
            fixnum_as_cell!(Fixnum::build_with(process.id())),
        );

        Ok(())
    }

    pub(crate) fn process_wait(&mut self) -> CallResult {
        fn stub_gen() -> Vec<FunctorElement> {
            functor_stub(atom!("process_wait"), 3)
        }

        // Process
        let process_r = self.deref_register(1);
        // Var | Status
        let status_r = self.deref_register(2);
        // timeout | 0
        let timeout_r = self.deref_register(3);

        let Some(ptr) = process_r.to_untyped_arena_ptr() else {
            let err = self.machine_st.type_error(ValidType::Process, process_r);
            return Err(self.machine_st.error_form(err, stub_gen()));
        };

        let mut process = match_untyped_arena_ptr!(ptr,
            (ArenaHeaderTag::ChildProcess, child_process) => {
                child_process
            }
            (ArenaHeaderTag::Dropped, _dropped) => {
                let err = self.machine_st.existence_error(ExistenceError::Process(process_r));
                return Err(self.machine_st.error_form(err, stub_gen()));
            }
            _ => {
                let err = self.machine_st.type_error(ValidType::Process, process_r);
                return Err(self.machine_st.error_form(err, stub_gen()));
            }
        );

        let status = if let Some(atom) = timeout_r.to_atom() {
            match atom {
                atom!("infinite") => process.wait().map(Some),
                _ => {
                    panic!("Invalid Timeout value")
                }
            }
        } else if let Some(timeout) = timeout_r.to_fixnum() {
            if timeout.get_num() == 0 {
                process.try_wait()
            } else {
                panic!("Invalid Timeout value")
            }
        } else {
            panic!("Invalid Timeout value")
        };

        match status {
            Ok(None) => {
                unify!(self.machine_st, status_r, atom_as_cell!(atom!("timeout")));
                Ok(())
            }
            Ok(Some(exit_status)) => {
                if let Some(exit_code) = exit_status.code() {
                    let mut writer =
                        Heap::functor_writer(functor!(atom!("exit"), [fixnum(exit_code)]));

                    match writer(&mut self.machine_st.heap) {
                        Ok(loc) => {
                            unify!(self.machine_st, status_r, loc);
                        }
                        Err(resource_err_loc) => {
                            self.machine_st.throw_resource_error(resource_err_loc);
                        }
                    }
                    Ok(())
                } else {
                    #[cfg(unix)]
                    {
                        use std::os::unix::process::ExitStatusExt;

                        if let Some(signal) = ExitStatusExt::signal(&exit_status) {
                            let mut writer =
                                Heap::functor_writer(functor!(atom!("killed"), [fixnum(signal)]));

                            match writer(&mut self.machine_st.heap) {
                                Ok(loc) => {
                                    unify!(self.machine_st, status_r, loc);
                                }
                                Err(resource_err_loc) => {
                                    self.machine_st.throw_resource_error(resource_err_loc);
                                }
                            }
                            Ok(())
                        } else {
                            let err = self.machine_st.unreachable_error();
                            Err(self.machine_st.error_form(err, stub_gen()))
                        }
                    }
                    #[cfg(not(unix))]
                    {
                        let err = self.machine_st.unreachable_error();
                        Err(self.machine_st.error_form(err, stub_gen()))
                    }
                }
            }
            Err(_) => {
                let perm_error = self.machine_st.permission_error(
                    Permission::Modify,
                    atom!("process"),
                    stub_gen(),
                );
                Err(self.machine_st.error_form(perm_error, stub_gen()))
            }
        }
    }

    pub(crate) fn process_kill(&mut self) -> CallResult {
        fn stub_gen() -> Vec<FunctorElement> {
            functor_stub(atom!("process_kill"), 1)
        }

        // Pid
        let process_r = self.deref_register(1);

        let Some(ptr) = process_r.to_untyped_arena_ptr() else {
            let err = self.machine_st.type_error(ValidType::Process, process_r);
            return Err(self.machine_st.error_form(err, stub_gen()));
        };

        let mut process = match_untyped_arena_ptr!(ptr,
            (ArenaHeaderTag::ChildProcess, child_process) => {
                child_process
            }
            (ArenaHeaderTag::Dropped, _dropped) => {
                let err = self.machine_st.existence_error(ExistenceError::Process(process_r));
                return Err(self.machine_st.error_form(err, stub_gen()));
            }
            _ => {
                let err = self.machine_st.type_error(ValidType::Process, process_r);
                return Err(self.machine_st.error_form(err, stub_gen()));
            }
        );

        if process.kill().is_err() {
            let perm_error =
                self.machine_st
                    .permission_error(Permission::Modify, atom!("process"), stub_gen());
            return Err(self.machine_st.error_form(perm_error, stub_gen()));
        }
        Ok(())
    }

    pub(crate) fn process_release(&mut self) -> CallResult {
        fn stub_gen() -> Vec<FunctorElement> {
            functor_stub(atom!("process_release"), 1)
        }

        let process = self.deref_register(1);

        if let Some(ptr) = process.to_untyped_arena_ptr() {
            match_untyped_arena_ptr!(ptr,
                (ArenaHeaderTag::ChildProcess, child_process) => {
                    child_process.drop_payload();

                    return Ok(());
                }
                _ => {
                }
            );
        }

        let err = self.machine_st.type_error(ValidType::Process, process);

        Err(self.machine_st.error_form(err, stub_gen()))
    }

    #[inline(always)]
    pub(crate) fn chars_base64(&mut self) -> CallResult {
        let padding = cell_as_atom!(self.deref_register(3));
        let charset = cell_as_atom!(self.deref_register(4));

        let b64_engine = match (padding, charset) {
            (atom!("true"), atom!("standard")) => base64::engine::general_purpose::STANDARD,
            (atom!("true"), _) => base64::engine::general_purpose::URL_SAFE,
            (_, atom!("standard")) => base64::engine::general_purpose::STANDARD_NO_PAD,
            (_, _) => base64::engine::general_purpose::URL_SAFE_NO_PAD,
        };

        if self.deref_register(1).is_var() {
            let b64 = self
                .machine_st
                .value_to_str_like(self.machine_st.registers[2])
                .unwrap();

            let bytes = b64_engine.decode(&*b64.as_str());

            match bytes {
                Ok(bs) => {
                    let string =
                        resource_error_call_result!(self.machine_st, self.u8s_to_string(&bs));

                    unify!(self.machine_st, self.machine_st.registers[1], string);
                }
                _ => {
                    self.machine_st.fail = true;
                    return Ok(());
                }
            }
        } else {
            let mut bytes = vec![];
            for c in self
                .machine_st
                .value_to_str_like(self.machine_st.registers[1])
                .unwrap()
                .as_str()
                .chars()
            {
                bytes.push(c as u8);
            }

            let b64 = b64_engine.encode(bytes);
            let string =
                resource_error_call_result!(self.machine_st, self.u8s_to_string(b64.as_bytes()));

            unify!(self.machine_st, self.machine_st.registers[2], string);
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn load_library_as_stream(&mut self) -> CallResult {
        let library_name = cell_as_atom!(self.deref_register(1));

        let lib = libraries::get(&library_name.as_str());
        match lib {
            Some(library) => {
                let lib_stream = Stream::from_static_string(library, &mut self.machine_st.arena);
                unify!(
                    self.machine_st,
                    HeapCellValue::from(lib_stream),
                    self.machine_st.registers[2]
                );

                let mut path_buf = machine::current_dir();

                path_buf.push("/lib");
                path_buf.push(&*library_name.as_str());

                let library_path_str = path_buf.to_str().unwrap();
                let library_path =
                    AtomTable::build_with(&self.machine_st.atom_tbl, library_path_str);

                self.machine_st
                    .unify_atom(library_path, self.machine_st.registers[3]);
            }
            None => {
                let stub = functor_stub(atom!("load"), 1);
                let err = self
                    .machine_st
                    .existence_error(ExistenceError::ModuleSource(ModuleSource::Library(
                        library_name,
                    )));

                return Err(self.machine_st.error_form(err, stub));
            }
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn devour_whitespace(&mut self) -> CallResult {
        let mut stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices,
            atom!("$devour_whitespace"),
            1,
        )?;

        let mut parser = Parser::new(stream, &mut self.machine_st);

        match devour_whitespace(&mut parser.lexer) {
            Ok(false) => {
                // not at EOF.
                stream.add_lines_read(parser.lines_read());
            }
            Ok(true) => {
                stream.add_lines_read(parser.lexer.line_num);
                self.machine_st.fail = true;
            }
            Err(err) => {
                let stub = functor_stub(atom!("load"), 1);
                let err = self.machine_st.syntax_error(err);

                return Err(self.machine_st.error_form(err, stub));
            }
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn is_sto_enabled(&mut self) {
        if self.machine_st.unify_fn as usize == MachineState::unify_with_occurs_check as usize {
            self.machine_st
                .unify_atom(atom!("true"), self.machine_st.registers[1]);
        } else if self.machine_st.unify_fn as usize
            == MachineState::unify_with_occurs_check_with_error as usize
        {
            self.machine_st
                .unify_atom(atom!("error"), self.machine_st.registers[1]);
        } else {
            self.machine_st
                .unify_atom(atom!("false"), self.machine_st.registers[1]);
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
                let path_string = step_or_resource_error!(
                    self.machine_st,
                    self.machine_st.heap.allocate_cstr(path)
                );

                unify!(self.machine_st, self.machine_st.registers[1], path_string);
                return;
            }
        }

        self.machine_st.fail = true;
    }

    pub(crate) fn debug_hook(&mut self) {}

    #[inline(always)]
    pub(crate) fn pop_count(&mut self) {
        let number = self.deref_register(1);
        let pop_count = integer_as_cell!(match Number::try_from((
            number,
            &self.machine_st.arena.f64_tbl
        )) {
            Ok(Number::Fixnum(n)) => {
                Number::Fixnum(Fixnum::build_with(n.get_num().count_ones()))
            }
            Ok(Number::Integer(n)) => {
                let value: usize = if n.sign() == Sign::Positive {
                    (*n).clone().into_parts().1.count_ones()
                } else {
                    0
                };
                Number::arena_from(value, &mut self.machine_st.arena)
            }
            _ => {
                unreachable!()
            }
        });

        unify!(self.machine_st, self.machine_st.registers[2], pop_count);
    }

    pub(super) fn systemtime_to_timestamp(&mut self, system_time: SystemTime) -> String {
        let datetime: DateTime<Local> = system_time.into();

        let mut fstr = "[".to_string();
        const SPECIFIERS: [char; 19] = [
            'Y', 'm', 'd', 'H', 'M', 'S', 'y', 'b', 'B', 'a', 'A', 'w', 'u', 'U', 'W', 'j', 'D',
            'x', 'v',
        ];

        for spec in SPECIFIERS {
            fstr.push_str(&format!("'{spec}'=\"%{spec}\", "));
        }

        fstr.push_str("finis].");
        datetime.format(&fstr).to_string()
    }

    pub(super) fn string_encoding_bytes(
        &mut self,
        data_arg: HeapCellValue,
        encoding: Atom,
    ) -> Vec<u8> {
        let data = self.machine_st.value_to_str_like(data_arg).unwrap();

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
        node: roxmltree::Node,
    ) -> Result<HeapCellValue, usize> {
        if node.is_text() {
            self.machine_st.heap.allocate_cstr(node.text().unwrap())
        } else {
            let mut avec = Vec::new();

            for attr in node.attributes() {
                let name = AtomTable::build_with(&self.machine_st.atom_tbl, attr.name());
                let value = self.machine_st.heap.allocate_cstr(attr.value())?;

                avec.push(str_loc_as_cell!(self.machine_st.heap.cell_len()));

                let mut writer = self.machine_st.heap.reserve(3)?;

                writer.write_with(|section| {
                    section.push_cell(atom_as_cell!(atom!("="), 2));
                    section.push_cell(atom_as_cell!(name));
                    section.push_cell(value);
                });
            }

            let attrs =
                sized_iter_to_heap_list(&mut self.machine_st.heap, avec.len(), avec.into_iter())?;

            let mut cvec = Vec::new();

            for child in node.children() {
                cvec.push(self.xml_node_to_term(child)?);
            }

            let children =
                sized_iter_to_heap_list(&mut self.machine_st.heap, cvec.len(), cvec.into_iter())?;

            let tag = AtomTable::build_with(&self.machine_st.atom_tbl, node.tag_name().name());
            let result = str_loc_as_cell!(self.machine_st.heap.cell_len());
            let mut writer = self.machine_st.heap.reserve(4)?;

            writer.write_with(|section| {
                section.push_cell(atom_as_cell!(atom!("element"), 3));
                section.push_cell(atom_as_cell!(tag));
                section.push_cell(attrs);
                section.push_cell(children);
            });

            Ok(result)
        }
    }

    pub(super) fn html_node_to_term(
        &mut self,
        node: ego_tree::NodeRef<'_, scraper::Node>,
    ) -> Result<HeapCellValue, usize> {
        match node.value() {
            scraper::Node::Document | scraper::Node::Fragment => {
                unreachable!("we never iterate the root itself only its children")
            }
            scraper::Node::Doctype(doctype) => {
                // what about public and system id?
                let name = self.machine_st.heap.allocate_cstr(&doctype.name)?;

                let result = str_loc_as_cell!(self.machine_st.heap.cell_len());
                let mut writer = self.machine_st.heap.reserve(2)?;

                writer.write_with(|section| {
                    section.push_cell(atom_as_cell!(atom!("doctype"), 1));
                    section.push_cell(name);
                });

                Ok(result)
            }
            scraper::Node::Comment(comment) => {
                let comment = self.machine_st.heap.allocate_cstr(comment)?;

                let result = str_loc_as_cell!(self.machine_st.heap.cell_len());
                let mut writer = self.machine_st.heap.reserve(2)?;

                writer.write_with(|section| {
                    section.push_cell(atom_as_cell!(atom!("comment"), 1));
                    section.push_cell(comment);
                });

                Ok(result)
            }
            scraper::Node::Text(text) => self.machine_st.heap.allocate_cstr(&text.text),
            scraper::Node::Element(element) => {
                let mut avec = Vec::new();

                for attr in element.attrs() {
                    let name = AtomTable::build_with(&self.machine_st.atom_tbl, attr.0);
                    let value = self.machine_st.heap.allocate_cstr(attr.1)?;

                    avec.push(str_loc_as_cell!(self.machine_st.heap.cell_len()));

                    let mut writer = self.machine_st.heap.reserve(3)?;

                    writer.write_with(|section| {
                        section.push_cell(atom_as_cell!(atom!("="), 2));
                        section.push_cell(atom_as_cell!(name));
                        section.push_cell(value);
                    });
                }

                let attrs = sized_iter_to_heap_list(
                    &mut self.machine_st.heap,
                    avec.len(),
                    avec.into_iter(),
                )?;

                let cvec = node
                    .children()
                    .map(|child| self.html_node_to_term(child))
                    .collect::<Result<Vec<_>, _>>()?;

                let children = sized_iter_to_heap_list(
                    &mut self.machine_st.heap,
                    cvec.len(),
                    cvec.into_iter(),
                )?;

                let tag = AtomTable::build_with(&self.machine_st.atom_tbl, element.name());
                let result = str_loc_as_cell!(self.machine_st.heap.cell_len());
                let mut writer = self.machine_st.heap.reserve(4)?;

                writer.write_with(|section| {
                    section.push_cell(atom_as_cell!(atom!("element"), 3));
                    section.push_cell(atom_as_cell!(tag));
                    section.push_cell(attrs);
                    section.push_cell(children);
                });

                Ok(result)
            }
            scraper::Node::ProcessingInstruction(processing_instruction) => {
                let target = self
                    .machine_st
                    .heap
                    .allocate_cstr(&processing_instruction.target)?;
                let data = self
                    .machine_st
                    .heap
                    .allocate_cstr(&processing_instruction.data)?;

                let result = str_loc_as_cell!(self.machine_st.heap.cell_len());
                let mut writer = self.machine_st.heap.reserve(3)?;

                writer.write_with(|section| {
                    section.push_cell(atom_as_cell!(atom!("processing_instruction"), 2));
                    section.push_cell(target);
                    section.push_cell(data);
                });

                Ok(result)
            }
        }
    }

    pub(super) fn u8s_to_string(&mut self, data: &[u8]) -> Result<HeapCellValue, usize> {
        let buffer = String::from_iter(data.iter().map(|b| *b as char));

        if buffer.is_empty() {
            Ok(empty_list_as_cell!())
        } else {
            self.machine_st.heap.allocate_cstr(&buffer)
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
