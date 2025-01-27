use crate::atom_table::*;
use crate::parser::ast::*;

use crate::machine::heap::*;
use crate::machine::machine_errors::CycleSearchResult;
use crate::machine::system_calls::BrentAlgState;
use crate::types::*;

use std::cmp::Ordering;
use std::ops::Deref;
use std::str;

#[derive(Copy, Clone, Debug)]
pub struct PartialString(Atom);

fn scan_for_terminator<Iter: Iterator<Item = char>>(iter: Iter) -> usize {
    let mut terminator_idx = 0;

    for c in iter {
        if c == '\u{0}' && terminator_idx != 0 {
            return terminator_idx;
        }

        terminator_idx += c.len_utf8();
    }

    terminator_idx
}

impl From<Atom> for PartialString {
    #[inline]
    fn from(buf: Atom) -> PartialString {
        PartialString(buf)
    }
}

impl From<PartialString> for Atom {
    #[inline]
    fn from(val: PartialString) -> Self {
        val.0
    }
}

impl PartialString {
    #[inline]
    pub(super) fn new<'a>(src: &'a str, atom_tbl: &AtomTable) -> Option<(Self, &'a str)> {
        let terminator_idx = scan_for_terminator(src.chars());
        let pstr = PartialString(AtomTable::build_with(atom_tbl, &src[..terminator_idx]));
        Some(if terminator_idx < src.as_bytes().len() {
            (pstr, &src[terminator_idx + 1..])
        } else {
            (pstr, "")
        })
    }

    #[inline(always)]
    pub(crate) fn as_str_from(&self, n: usize) -> AtomString {
        self.0.as_str().map(|str| &str[n..])
    }
}

#[derive(Clone, Copy)]
pub struct HeapPStrIter<'a> {
    pub heap: &'a [HeapCellValue],
    pub focus: HeapCellValue,
    orig_focus: usize,
    brent_st: BrentAlgState,
    stepper: fn(&mut HeapPStrIter<'a>) -> Option<PStrIteratee>,
}

#[derive(Debug, Clone, Copy)]
pub struct PStrPrefixCmpResult {
    pub focus: usize,
    pub offset: usize,
    pub prefix_len: usize,
}

struct PStrIterStep {
    iteratee: PStrIteratee,
    next_hare: usize,
}

impl<'a> HeapPStrIter<'a> {
    pub fn new(heap: &'a [HeapCellValue], h: usize) -> Self {
        let value = heap[h];

        Self {
            heap,
            focus: value,
            orig_focus: h,
            brent_st: BrentAlgState::new(h),
            stepper: HeapPStrIter::pre_cycle_discovery_stepper,
        }
    }

    #[inline(always)]
    pub fn focus(&self) -> usize {
        self.brent_st.hare
    }

    #[inline(always)]
    pub fn at_string_terminator(&self) -> bool {
        self.focus.is_string_terminator(self.heap)
    }

    #[inline(always)]
    pub fn chars(mut self) -> PStrCharsIter<'a> {
        let item = self.next();
        PStrCharsIter { iter: self, item }
    }

    pub fn compare_pstr_to_string(&mut self, s: &str) -> Option<PStrPrefixCmpResult> {
        let mut result = PStrPrefixCmpResult {
            focus: self.brent_st.hare,
            offset: 0,
            prefix_len: 0,
        };

        let mut final_result = None;

        while let Some(PStrIterStep {
            iteratee,
            next_hare,
        }) = self.step(self.brent_st.hare)
        {
            self.brent_st.hare = next_hare;
            self.focus = self.heap[iteratee.focus()];

            result.focus = iteratee.focus();
            result.offset = iteratee.offset();

            match iteratee {
                PStrIteratee::Char(_, c1) => {
                    if let Some(c2) = s[result.prefix_len..].chars().next() {
                        if c1 != c2 {
                            return None;
                        } else {
                            result.prefix_len += c1.len_utf8();
                            result.offset += c1.len_utf8();
                        }
                    } else {
                        final_result = Some(result);
                        break;
                    }
                }
                PStrIteratee::PStrSegment(_, pstr_atom, n) => {
                    let pstr = PartialString::from(pstr_atom);
                    let t = pstr.as_str_from(n);
                    let s = &s[result.prefix_len..];

                    if s.len() >= t.len() {
                        if s.starts_with(&*t) {
                            result.prefix_len += t.len();
                            result.offset += t.len();
                        } else {
                            return None;
                        }
                    } else if t.starts_with(s) {
                        result.prefix_len += s.len();
                        result.offset += s.len();

                        final_result = Some(result);
                        break;
                    } else {
                        return None;
                    }
                }
            }

            if s.len() == result.prefix_len {
                final_result = Some(result);
                break;
            }
        }

        if let Some(result) = &final_result {
            if self.at_string_terminator() {
                self.focus = empty_list_as_cell!();
                self.brent_st.hare = result.focus;
            } else {
                read_heap_cell!(self.heap[result.focus],
                    (HeapCellValueTag::Lis | HeapCellValueTag::Str | HeapCellValueTag::PStr) => {
                        self.focus = self.heap[self.brent_st.hare];
                    }
                    _ => {
                    }
                );
            }
        }

        Some(result)
    }

    fn walk_hare_to_cycle_end(&mut self) {
        // walk_hare_to_cycle_end assumes a cycle has been found,
        // so it is always safe to unwrap self.step()

        let orig_hare = self.brent_st.hare;

        self.brent_st.hare = self.orig_focus;
        self.brent_st.tortoise = self.orig_focus;

        for _ in 0..self.brent_st.lam {
            self.brent_st.hare = self.step(self.brent_st.hare).unwrap().next_hare;
        }

        while self.brent_st.hare != self.brent_st.tortoise {
            self.brent_st.tortoise = self.step(self.brent_st.tortoise).unwrap().next_hare;
            self.brent_st.hare = self.step(self.brent_st.hare).unwrap().next_hare;
        }

        self.focus = self.heap[orig_hare];
        self.brent_st.hare = orig_hare;
    }

    pub fn to_string_mut(&mut self) -> String {
        let mut buf = String::with_capacity(32);

        for iteratee in self.by_ref() {
            match iteratee {
                PStrIteratee::Char(_, c) => {
                    buf.push(c);
                }
                PStrIteratee::PStrSegment(_, pstr_atom, n) => {
                    let pstr = PartialString::from(pstr_atom);
                    buf += &*pstr.as_str_from(n);
                }
            }
        }

        buf
    }

    #[inline]
    pub fn is_continuable(&self) -> bool {
        let mut focus = self.focus;

        loop {
            read_heap_cell!(focus,
                (HeapCellValueTag::CStr | HeapCellValueTag::PStrLoc) => {
                    return true;
                }
                (HeapCellValueTag::Atom, (name, arity)) => { // TODO: use Str here?
                    return name == atom!(".") && arity == 2;
                }
                (HeapCellValueTag::Lis, h) => {
                    let value = self.heap[h];
                    let value = heap_bound_store(
                        self.heap,
                        heap_bound_deref(self.heap, value),
                    );

                    return read_heap_cell!(value,
                        (HeapCellValueTag::Atom, (name, arity)) => {
                            arity == 0 && name.as_char().is_some()
                        }
                        (HeapCellValueTag::Char) => {
                            true
                        }
                        _ => {
                            false
                        }
                    );
                }
                (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
                    if focus == self.heap[h] {
                        return false;
                    }

                    focus = self.heap[h];
                }
                _ => {
                    return false;
                }
            );
        }
    }

    #[inline(always)]
    pub fn cycle_detected(&self) -> bool {
        self.stepper as usize == HeapPStrIter::post_cycle_discovery_stepper as usize
    }

    fn step(&self, mut curr_hare: usize) -> Option<PStrIterStep> {
        loop {
            read_heap_cell!(self.heap[curr_hare],
                (HeapCellValueTag::CStr, cstr_atom) => {
                    return if self.focus == empty_list_as_cell!() {
                        None
                    } else {
                        Some(PStrIterStep {
                            iteratee: PStrIteratee::PStrSegment(curr_hare, cstr_atom, 0),
                            next_hare: curr_hare,
                        })
                    }
                }
                (HeapCellValueTag::PStrLoc, h) => {
                    curr_hare = h;
                }
                (HeapCellValueTag::PStr, pstr_atom) => {
                    return Some(PStrIterStep {
                        iteratee: PStrIteratee::PStrSegment(curr_hare, pstr_atom, 0),
                        next_hare: curr_hare+1,
                    });
                }
                (HeapCellValueTag::PStrOffset, pstr_offset) => {
                    if self.focus == empty_list_as_cell!() {
                        return None;
                    }

                    let pstr_atom = cell_as_atom!(self.heap[pstr_offset]);
                    let n = cell_as_fixnum!(self.heap[curr_hare+1]).get_num() as usize;

                    return if self.heap[pstr_offset].get_tag() == HeapCellValueTag::CStr {
                        Some(PStrIterStep {
                            iteratee: PStrIteratee::PStrSegment(curr_hare, pstr_atom, n),
                            next_hare: pstr_offset,
                        })
                    } else {
                        Some(PStrIterStep {
                            iteratee: PStrIteratee::PStrSegment(curr_hare, pstr_atom, n),
                            next_hare: pstr_offset+1,
                        })
                    };
                }
                (HeapCellValueTag::Lis, h) => {
                    let value = heap_bound_store(
                        self.heap,
                        heap_bound_deref(self.heap, self.heap[h]),
                    );

                    return value.as_char().map(|c| PStrIterStep {
                        iteratee: PStrIteratee::Char(curr_hare, c),
                        next_hare: h+1,
                    });
                }
                (HeapCellValueTag::Str, s) => {
                    let (name, arity) = cell_as_atom_cell!(self.heap[s])
                        .get_name_and_arity();

                    return if name == atom!(".") && arity == 2 {
                        let value = heap_bound_store(
                            self.heap,
                            heap_bound_deref(self.heap, self.heap[s+1]),
                        );

                        value.as_char().map(|c| PStrIterStep {
                            iteratee: PStrIteratee::Char(curr_hare, c),
                            next_hare: s+2,
                        })
                    } else {
                        None
                    };
                }
                (HeapCellValueTag::Atom, (_name, arity)) => {
                    debug_assert!(arity == 0);
                    return None;
                }
                (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
                    if h == curr_hare {
                        return None;
                    }

                    curr_hare = h;
                }
                _ => {
                    return None;
                }
            );
        }
    }

    fn pre_cycle_discovery_stepper(&mut self) -> Option<PStrIteratee> {
        let PStrIterStep {
            iteratee,
            next_hare,
        } = match self.step(self.brent_st.hare) {
            Some(results) => results,
            None => {
                return None;
            }
        };

        self.focus = self.heap[iteratee.focus()];

        if self.at_string_terminator() {
            self.focus = empty_list_as_cell!();
            self.brent_st.hare = iteratee.focus();

            return Some(iteratee);
        }

        match self.brent_st.step(next_hare) {
            Some(cycle_result) => {
                debug_assert!(matches!(cycle_result, CycleSearchResult::Cyclic(..)));

                self.walk_hare_to_cycle_end();
                self.stepper = HeapPStrIter::post_cycle_discovery_stepper;
            }
            None => {
                self.focus = self.heap[next_hare];
            }
        }

        Some(iteratee)
    }

    fn post_cycle_discovery_stepper(&mut self) -> Option<PStrIteratee> {
        if self.brent_st.hare == self.brent_st.tortoise {
            return None;
        }

        let PStrIterStep {
            iteratee,
            next_hare,
        } = match self.step(self.brent_st.hare) {
            Some(results) => results,
            None => {
                return None;
            }
        };

        self.focus = self.heap[next_hare];
        self.brent_st.hare = next_hare;

        Some(iteratee)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PStrIteratee {
    Char(usize, char),
    PStrSegment(usize, Atom, usize),
}

impl PStrIteratee {
    #[inline]
    fn offset(&self) -> usize {
        match self {
            PStrIteratee::Char(_, _) => 0,
            PStrIteratee::PStrSegment(_, _, n) => *n,
        }
    }

    #[inline]
    fn focus(&self) -> usize {
        match self {
            PStrIteratee::Char(focus, _) => *focus,
            PStrIteratee::PStrSegment(focus, _, _) => *focus,
        }
    }
}

impl<'a> Iterator for HeapPStrIter<'a> {
    type Item = PStrIteratee;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        (self.stepper)(self)
    }
}

pub struct PStrCharsIter<'a> {
    pub iter: HeapPStrIter<'a>,
    pub item: Option<PStrIteratee>,
}

impl<'a> PStrCharsIter<'a> {
    pub fn peek(&self) -> Option<char> {
        if let Some(iteratee) = self.item {
            match iteratee {
                PStrIteratee::Char(_, c) => {
                    return Some(c);
                }
                PStrIteratee::PStrSegment(_, pstr_atom, n) => {
                    let pstr = PartialString::from(pstr_atom);
                    return pstr.as_str_from(n).chars().next();
                }
            }
        }

        None
    }
}

impl<'a> Deref for PStrCharsIter<'a> {
    type Target = HeapPStrIter<'a>;

    fn deref(&self) -> &Self::Target {
        &self.iter
    }
}

impl<'a> Iterator for PStrCharsIter<'a> {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(item) = self.item {
            match item {
                PStrIteratee::Char(_, c) => {
                    self.item = self.iter.next();
                    return Some(c);
                }
                PStrIteratee::PStrSegment(f1, pstr_atom, n) => {
                    let pstr = PartialString::from(pstr_atom);

                    match pstr.as_str_from(n).chars().next() {
                        Some(c) => {
                            self.item =
                                Some(PStrIteratee::PStrSegment(f1, pstr_atom, n + c.len_utf8()));

                            return Some(c);
                        }
                        None => {
                            self.item = self.iter.next();
                        }
                    }
                }
            }
        }

        None
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PStrCmpResult {
    Ordered(Ordering),
    FirstIterContinuable(PStrIteratee),
    SecondIterContinuable(PStrIteratee),
    Unordered,
}

impl PStrCmpResult {
    #[inline]
    pub fn is_second_iter(&self) -> bool {
        matches!(self, PStrCmpResult::SecondIterContinuable(_))
    }
}

#[inline]
pub fn compare_pstr_prefixes<'a>(
    i1: &mut HeapPStrIter<'a>,
    i2: &mut HeapPStrIter<'a>,
) -> PStrCmpResult {
    #[inline(always)]
    fn step(iter: &mut HeapPStrIter, hare: usize) -> Option<PStrIterStep> {
        let result = iter.step(hare);
        iter.focus = iter.heap[hare];

        if iter.focus.is_string_terminator(iter.heap) {
            iter.focus = empty_list_as_cell!();
        }

        result
    }

    #[inline(always)]
    fn cycle_detection_step(i1: &mut HeapPStrIter, i2: &HeapPStrIter, step: &PStrIterStep) -> bool {
        if i1.cycle_detected() {
            i1.brent_st.hare = step.next_hare;
            i2.cycle_detected()
        } else if i1.brent_st.step(step.next_hare).is_some() {
            i1.stepper = HeapPStrIter::post_cycle_discovery_stepper;
            i2.cycle_detected()
        } else {
            false
        }
    }

    let mut r1 = step(i1, i1.brent_st.hare);
    let mut r2 = step(i2, i2.brent_st.hare);

    loop {
        if let Some(step_1) = r1.as_mut() {
            if let Some(step_2) = r2.as_mut() {
                match (step_1.iteratee, step_2.iteratee) {
                    (PStrIteratee::Char(_, c1), PStrIteratee::Char(_, c2)) => {
                        if c1 != c2 {
                            return PStrCmpResult::Ordered(c1.cmp(&c2));
                        }

                        cycle_detection_step(i1, i2, step_1);
                        let both_cyclic = cycle_detection_step(i2, i1, step_2);

                        r1 = step(i1, i1.brent_st.hare);
                        r2 = step(i2, i2.brent_st.hare);

                        if !both_cyclic {
                            continue;
                        }
                    }
                    (PStrIteratee::Char(_, c1), PStrIteratee::PStrSegment(f2, pstr_atom, n)) => {
                        let pstr = PartialString::from(pstr_atom);

                        if let Some(c2) = pstr.as_str_from(n).chars().next() {
                            if c1 != c2 {
                                return PStrCmpResult::Ordered(c1.cmp(&c2));
                            }

                            let n1 = n + c2.len_utf8();

                            if n1 < pstr_atom.len() {
                                step_2.iteratee = PStrIteratee::PStrSegment(f2, pstr_atom, n1);

                                let c1_result = cycle_detection_step(i1, i2, step_1);
                                r1 = step(i1, i1.brent_st.hare);

                                if !c1_result {
                                    continue;
                                }
                            } else {
                                cycle_detection_step(i1, i2, step_1);
                                let both_cyclic = cycle_detection_step(i2, i1, step_2);

                                r1 = step(i1, i1.brent_st.hare);
                                r2 = step(i2, i2.brent_st.hare);

                                if !both_cyclic {
                                    continue;
                                }
                            }
                        } else {
                            let c2_result = cycle_detection_step(i2, i1, step_2);
                            r2 = step(i2, i2.brent_st.hare);

                            if !c2_result {
                                continue;
                            }
                        }
                    }
                    (PStrIteratee::PStrSegment(f1, pstr_atom, n), PStrIteratee::Char(_, c2)) => {
                        let pstr = PartialString::from(pstr_atom);

                        if let Some(c1) = pstr.as_str_from(n).chars().next() {
                            if c1 != c2 {
                                return PStrCmpResult::Ordered(c1.cmp(&c2));
                            }

                            let n1 = n + c1.len_utf8();

                            if n1 < pstr_atom.len() {
                                step_1.iteratee = PStrIteratee::PStrSegment(f1, pstr_atom, n1);

                                let c2_result = cycle_detection_step(i2, i1, step_2);
                                r2 = step(i2, step_2.next_hare);

                                if !c2_result {
                                    continue;
                                }
                            } else {
                                cycle_detection_step(i1, i2, step_1);
                                let both_cyclic = cycle_detection_step(i2, i1, step_2);

                                r1 = step(i1, i1.brent_st.hare);
                                r2 = step(i2, i2.brent_st.hare);

                                if !both_cyclic {
                                    continue;
                                }
                            }
                        } else {
                            let c1_result = cycle_detection_step(i1, i2, step_1);
                            r1 = step(i1, i1.brent_st.hare);

                            if !c1_result {
                                continue;
                            }
                        }
                    }
                    (
                        PStrIteratee::PStrSegment(f1, pstr1_atom, n1),
                        PStrIteratee::PStrSegment(f2, pstr2_atom, n2),
                    ) => {
                        if pstr1_atom == pstr2_atom && n1 == n2 {
                            cycle_detection_step(i1, i2, step_1);
                            let both_cyclic = cycle_detection_step(i2, i1, step_2);

                            r1 = step(i1, i1.brent_st.hare);
                            r2 = step(i2, i2.brent_st.hare);

                            if !both_cyclic {
                                continue;
                            }

                            break;
                        }

                        let pstr1 = PartialString::from(pstr1_atom);
                        let pstr2 = PartialString::from(pstr2_atom);

                        let str1 = pstr1.as_str_from(n1);
                        let str2 = pstr2.as_str_from(n2);

                        match str1.len().cmp(&str2.len()) {
                            Ordering::Equal if *str1 == *str2 => {
                                cycle_detection_step(i1, i2, step_1);
                                let both_cyclic = cycle_detection_step(i2, i1, step_2);

                                r1 = step(i1, i1.brent_st.hare);
                                r2 = step(i2, i2.brent_st.hare);

                                if !both_cyclic {
                                    continue;
                                }
                            }
                            Ordering::Less if str2.starts_with(&*str1) => {
                                step_2.iteratee =
                                    PStrIteratee::PStrSegment(f2, pstr2_atom, n2 + str1.len());
                                let c1_result = cycle_detection_step(i1, i2, step_1);
                                r1 = step(i1, i1.brent_st.hare);

                                if !c1_result {
                                    continue;
                                }
                            }
                            Ordering::Greater if str1.starts_with(&*str2) => {
                                step_1.iteratee =
                                    PStrIteratee::PStrSegment(f1, pstr1_atom, n1 + str2.len());
                                let c2_result = cycle_detection_step(i2, i1, step_2);
                                r2 = step(i2, i2.brent_st.hare);

                                if !c2_result {
                                    continue;
                                }
                            }
                            _ => {
                                return PStrCmpResult::Ordered(str1.cmp(&*str2));
                            }
                        }
                    }
                }
            }
        }

        break;
    }

    // to have a cyclic term, the cell at i1.focus must be:
    //
    // 1) 'continuable' as a cell in a string traversal, and,
    // 2) matchable by compare_pstr_prefixes to the cell at i2.focus.
    //
    // If both cells are continuable they must have been encountered
    // and thus matched by the compare_pstr_prefixes loop previously,
    // so here it suffices to check if they are both continuable.

    let r1_at_end = r1.is_none();
    let r2_at_end = r2.is_none();

    if r1_at_end && r2_at_end {
        if i1.focus == i2.focus {
            PStrCmpResult::Ordered(Ordering::Equal)
        } else {
            PStrCmpResult::Unordered
        }
    } else if r1_at_end {
        if i1.focus == empty_list_as_cell!() {
            PStrCmpResult::Ordered(Ordering::Less)
        } else {
            let r2_step = r2.unwrap();

            // advance i2 to the next character so the same character
            // isn't repeated
            if matches!(r2_step.iteratee, PStrIteratee::Char(..)) {
                cycle_detection_step(i2, i1, &r2_step);
            }

            PStrCmpResult::SecondIterContinuable(r2_step.iteratee)
        }
    } else if r2_at_end {
        if i2.focus == empty_list_as_cell!() {
            PStrCmpResult::Ordered(Ordering::Greater)
        } else {
            let r1_step = r1.unwrap();

            // advance i1 to the next character so the same character
            // isn't repeated
            if matches!(r1_step.iteratee, PStrIteratee::Char(..)) {
                cycle_detection_step(i1, i2, &r1_step);
            }

            PStrCmpResult::FirstIterContinuable(r1_step.iteratee)
        }
    } else if i1.is_continuable() && i2.is_continuable() {
        PStrCmpResult::Ordered(Ordering::Equal)
    } else {
        PStrCmpResult::Unordered
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::machine::mock_wam::*;

    #[test]
    #[cfg_attr(miri, ignore = "it takes too long to run")]
    fn pstr_iter_tests() {
        let mut wam = MockWAM::new();

        let pstr_var_cell =
            put_partial_string(&mut wam.machine_st.heap, "abc ", &wam.machine_st.atom_tbl);

        let pstr_cell = wam.machine_st.heap[pstr_var_cell.get_value() as usize];

        {
            let mut iter = HeapPStrIter::new(&wam.machine_st.heap, 0);

            assert_eq!(
                iter.next(),
                Some(PStrIteratee::PStrSegment(0, cell_as_atom!(pstr_cell), 0))
            );
            assert_eq!(iter.next(), None);

            assert!(!iter.at_string_terminator());
        }

        wam.machine_st.heap.pop();
        wam.machine_st.heap.push(pstr_loc_as_cell!(2));

        let pstr_second_var_cell =
            put_partial_string(&mut wam.machine_st.heap, "def", &wam.machine_st.atom_tbl);

        let pstr_second_cell = wam.machine_st.heap[pstr_second_var_cell.get_value() as usize];

        {
            let mut iter = HeapPStrIter::new(&wam.machine_st.heap, 0);

            assert_eq!(
                iter.next(),
                Some(PStrIteratee::PStrSegment(0, cell_as_atom!(pstr_cell), 0))
            );
            assert_eq!(
                iter.next(),
                Some(PStrIteratee::PStrSegment(
                    2,
                    cell_as_atom!(pstr_second_cell),
                    0
                ))
            );

            assert_eq!(iter.next(), None);
            assert!(!iter.at_string_terminator());
        }

        wam.machine_st.heap.pop();
        wam.machine_st.heap.push(empty_list_as_cell!());

        {
            let mut iter = HeapPStrIter::new(&wam.machine_st.heap, 0);

            assert_eq!(
                iter.next(),
                Some(PStrIteratee::PStrSegment(0, cell_as_atom!(pstr_cell), 0))
            );
            assert_eq!(
                iter.next(),
                Some(PStrIteratee::PStrSegment(
                    2,
                    cell_as_atom!(pstr_second_cell),
                    0
                ))
            );

            assert_eq!(iter.next(), None);
            assert!(iter.at_string_terminator());
        }

        wam.machine_st.heap.pop();
        wam.machine_st
            .heap
            .push(pstr_loc_as_cell!(wam.machine_st.heap.len() + 1));

        wam.machine_st.heap.push(pstr_offset_as_cell!(0));
        wam.machine_st
            .heap
            .push(fixnum_as_cell!(Fixnum::build_with(0)));

        {
            let mut iter = HeapPStrIter::new(&wam.machine_st.heap, 0);

            for _ in iter.by_ref() {}

            assert!(!iter.at_string_terminator());
        }

        {
            let mut iter1 = HeapPStrIter::new(&wam.machine_st.heap, 0);
            let mut iter2 = HeapPStrIter::new(&wam.machine_st.heap, 0);

            assert_eq!(
                compare_pstr_prefixes(&mut iter1, &mut iter2),
                PStrCmpResult::Ordered(Ordering::Equal)
            );
        }

        {
            let second_h = wam.machine_st.heap.len();

            // construct a structurally similar but different cyclic partial string
            // matching the one beginning at wam.machine_st.heap[0].

            put_partial_string(&mut wam.machine_st.heap, "ab", &wam.machine_st.atom_tbl);

            wam.machine_st.heap.pop();

            wam.machine_st.heap.push(pstr_loc_as_cell!(second_h + 2));

            put_partial_string(&mut wam.machine_st.heap, "c ", &wam.machine_st.atom_tbl);

            wam.machine_st.heap.pop();

            wam.machine_st.heap.push(pstr_loc_as_cell!(second_h + 4));

            wam.machine_st.heap.push(pstr_second_cell);
            wam.machine_st.heap.push(pstr_loc_as_cell!(second_h + 6));

            wam.machine_st.heap.push(pstr_offset_as_cell!(second_h));
            wam.machine_st
                .heap
                .push(fixnum_as_cell!(Fixnum::build_with(0)));

            let mut iter1 = HeapPStrIter::new(&wam.machine_st.heap, 0);
            let mut iter2 = HeapPStrIter::new(&wam.machine_st.heap, second_h);

            assert_eq!(
                compare_pstr_prefixes(&mut iter1, &mut iter2),
                PStrCmpResult::Ordered(Ordering::Equal)
            );
        }

        wam.machine_st.heap.clear();

        put_partial_string(&mut wam.machine_st.heap, "abc ", &wam.machine_st.atom_tbl);

        let pstr_cell = wam.machine_st.heap[0];

        wam.machine_st.heap[1] = list_loc_as_cell!(2);

        wam.machine_st.heap.push(char_as_cell!('a'));
        wam.machine_st.heap.push(list_loc_as_cell!(4));
        wam.machine_st.heap.push(char_as_cell!('b'));
        wam.machine_st.heap.push(empty_list_as_cell!());

        wam.machine_st.heap.push(pstr_cell);
        wam.machine_st.heap.push(heap_loc_as_cell!(7));

        {
            let mut iter1 = HeapPStrIter::new(&wam.machine_st.heap, 0);
            let mut iter2 = HeapPStrIter::new(&wam.machine_st.heap, 6);

            assert_eq!(
                compare_pstr_prefixes(&mut iter1, &mut iter2),
                PStrCmpResult::FirstIterContinuable(PStrIteratee::Char(1, 'a')),
            );

            assert_eq!(iter2.focus, heap_loc_as_cell!(7));
        }

        // test "abc" = [X,Y,Z].

        wam.machine_st.heap.clear();

        let cstr_var_cell =
            put_complete_string(&mut wam.machine_st.heap, "abc", &wam.machine_st.atom_tbl);

        wam.machine_st.heap.push(list_loc_as_cell!(2));
        wam.machine_st.heap.push(heap_loc_as_cell!(2));

        wam.machine_st.heap.push(list_loc_as_cell!(4));
        wam.machine_st.heap.push(heap_loc_as_cell!(4));

        wam.machine_st.heap.push(list_loc_as_cell!(6));
        wam.machine_st.heap.push(heap_loc_as_cell!(6));

        wam.machine_st.heap.push(empty_list_as_cell!());

        unify!(wam.machine_st, cstr_var_cell, heap_loc_as_cell!(1));

        assert_eq!(wam.machine_st.heap[2], char_as_cell!('a'),);

        assert_eq!(wam.machine_st.heap[4], char_as_cell!('b'),);

        assert_eq!(wam.machine_st.heap[6], char_as_cell!('c'),);

        // test "abc" = [X,Y,Z|D].

        wam.machine_st.heap.clear();

        let cstr_var_cell =
            put_complete_string(&mut wam.machine_st.heap, "abc", &wam.machine_st.atom_tbl);

        wam.machine_st.heap.push(list_loc_as_cell!(2));
        wam.machine_st.heap.push(heap_loc_as_cell!(2)); // X

        wam.machine_st.heap.push(list_loc_as_cell!(4));
        wam.machine_st.heap.push(heap_loc_as_cell!(4)); // Y

        wam.machine_st.heap.push(list_loc_as_cell!(6));
        wam.machine_st.heap.push(heap_loc_as_cell!(6)); // Z

        wam.machine_st.heap.push(heap_loc_as_cell!(7)); // D

        unify!(wam.machine_st, cstr_var_cell, heap_loc_as_cell!(1));

        assert!(!wam.machine_st.fail);

        assert_eq!(wam.machine_st.heap[2], char_as_cell!('a'),);

        assert_eq!(wam.machine_st.heap[4], char_as_cell!('b'),);

        assert_eq!(wam.machine_st.heap[6], char_as_cell!('c'),);

        assert_eq!(wam.machine_st.heap[7], empty_list_as_cell!(),);

        // test "d" = [d].

        wam.machine_st.heap.clear();

        let cstr_var_cell =
            put_complete_string(&mut wam.machine_st.heap, "d", &wam.machine_st.atom_tbl);

        wam.machine_st.heap.push(list_loc_as_cell!(2));
        wam.machine_st.heap.push(char_as_cell!('d'));
        wam.machine_st.heap.push(empty_list_as_cell!());

        unify!(wam.machine_st, cstr_var_cell, heap_loc_as_cell!(1));

        assert!(!wam.machine_st.fail);

        // test "abc" = [X,b,Z].

        wam.machine_st.heap.clear();

        let cstr_var_cell =
            put_complete_string(&mut wam.machine_st.heap, "abc", &wam.machine_st.atom_tbl);

        wam.machine_st.heap.push(list_loc_as_cell!(2));
        wam.machine_st.heap.push(heap_loc_as_cell!(2));

        wam.machine_st.heap.push(list_loc_as_cell!(4));
        wam.machine_st.heap.push(char_as_cell!('b'));

        wam.machine_st.heap.push(list_loc_as_cell!(6));
        wam.machine_st.heap.push(heap_loc_as_cell!(6));

        wam.machine_st.heap.push(empty_list_as_cell!());

        unify!(wam.machine_st, cstr_var_cell, heap_loc_as_cell!(1));

        assert!(!wam.machine_st.fail);

        assert_eq!(wam.machine_st.heap[2], char_as_cell!('a'),);

        assert_eq!(wam.machine_st.heap[4], char_as_cell!('b'),);

        assert_eq!(wam.machine_st.heap[6], char_as_cell!('c'),);

        // test "abcdef" = [a,b,c|X].

        wam.machine_st.heap.clear();

        put_complete_string(&mut wam.machine_st.heap, "abcdef", &wam.machine_st.atom_tbl);

        wam.machine_st.heap.push(pstr_as_cell!(atom!("abc")));
        wam.machine_st.heap.push(heap_loc_as_cell!(2));

        unify!(wam.machine_st, heap_loc_as_cell!(0), pstr_loc_as_cell!(1));

        print_heap_terms(wam.machine_st.heap.iter(), 0);

        assert!(!wam.machine_st.fail);

        assert_eq!(wam.machine_st.heap[2], pstr_loc_as_cell!(5));
        assert_eq!(wam.machine_st.heap[3], pstr_loc_as_cell!(1));
        assert_eq!(wam.machine_st.heap[4], atom_as_cstr_cell!(atom!("abcdef")));
        assert_eq!(wam.machine_st.heap[5], pstr_offset_as_cell!(4));
        assert_eq!(
            wam.machine_st.heap[6],
            fixnum_as_cell!(Fixnum::build_with_unchecked("abc".len() as i64))
        );

        // test iteration on X = [b,c,b,c,b,c,b,c|...] as an offset.

        wam.machine_st.heap.clear();

        wam.machine_st.heap.push(pstr_as_cell!(atom!("abc")));
        wam.machine_st.heap.push(pstr_loc_as_cell!(2));
        wam.machine_st.heap.push(pstr_offset_as_cell!(0));
        wam.machine_st
            .heap
            .push(fixnum_as_cell!(Fixnum::build_with(1)));

        {
            let mut iter = HeapPStrIter::new(&wam.machine_st.heap, 2);

            assert_eq!(
                iter.next(),
                Some(PStrIteratee::PStrSegment(2, atom!("abc"), 1))
            );

            for _ in iter {}
        }

        // #2293, test1.

        wam.machine_st.heap.clear();

        wam.machine_st.heap.push(atom_as_cstr_cell!(atom!("a ")));
        wam.machine_st.heap.push(heap_loc_as_cell!(1));
        wam.machine_st.heap.push(list_loc_as_cell!(3));
        wam.machine_st.heap.push(char_as_cell!(' '));
        wam.machine_st.heap.push(empty_list_as_cell!());

        unify!(wam.machine_st, list_loc_as_cell!(1), heap_loc_as_cell!(0));

        assert!(!wam.machine_st.fail);

        // #2293, test2.

        wam.machine_st.heap.clear();

        wam.machine_st.heap.push(atom_as_cstr_cell!(atom!(" a")));
        wam.machine_st.heap.push(char_as_cell!(' '));
        wam.machine_st.heap.push(list_loc_as_cell!(3));
        wam.machine_st.heap.push(heap_loc_as_cell!(3));
        wam.machine_st.heap.push(empty_list_as_cell!());

        unify!(wam.machine_st, list_loc_as_cell!(1), heap_loc_as_cell!(0));

        assert!(!wam.machine_st.fail);

        // #2293, test3.

        wam.machine_st.heap.clear();

        wam.machine_st.heap.push(atom_as_cstr_cell!(atom!("a b")));
        wam.machine_st.heap.push(heap_loc_as_cell!(1));
        wam.machine_st.heap.push(list_loc_as_cell!(3));
        wam.machine_st.heap.push(char_as_cell!(' '));
        wam.machine_st.heap.push(list_loc_as_cell!(5));
        wam.machine_st.heap.push(heap_loc_as_cell!(5));
        wam.machine_st.heap.push(empty_list_as_cell!());

        unify!(wam.machine_st, list_loc_as_cell!(1), heap_loc_as_cell!(0));

        assert!(!wam.machine_st.fail);

        // #2293, test4.

        wam.machine_st.heap.clear();

        wam.machine_st.heap.push(atom_as_cstr_cell!(atom!(" a ")));
        wam.machine_st.heap.push(char_as_cell!(' '));
        wam.machine_st.heap.push(list_loc_as_cell!(3));
        wam.machine_st.heap.push(heap_loc_as_cell!(3));
        wam.machine_st.heap.push(list_loc_as_cell!(5));
        wam.machine_st.heap.push(char_as_cell!(' '));
        wam.machine_st.heap.push(empty_list_as_cell!());

        unify!(wam.machine_st, list_loc_as_cell!(1), heap_loc_as_cell!(0));

        assert!(!wam.machine_st.fail);

        // #2293, test5.

        wam.machine_st.heap.clear();

        wam.machine_st.heap.push(atom_as_cstr_cell!(atom!(" a bc")));
        wam.machine_st.heap.push(char_as_cell!(' '));
        wam.machine_st.heap.push(list_loc_as_cell!(3));
        wam.machine_st.heap.push(heap_loc_as_cell!(3));
        wam.machine_st.heap.push(list_loc_as_cell!(5));
        wam.machine_st.heap.push(char_as_cell!(' '));
        wam.machine_st.heap.push(heap_loc_as_cell!(6));

        unify!(wam.machine_st, list_loc_as_cell!(1), heap_loc_as_cell!(0));

        assert!(!wam.machine_st.fail);

        // #2293, test6.

        wam.machine_st.heap.clear();

        wam.machine_st.heap.push(atom_as_cstr_cell!(atom!("abc")));
        wam.machine_st.heap.push(heap_loc_as_cell!(1));
        wam.machine_st.heap.push(list_loc_as_cell!(3));
        wam.machine_st.heap.push(char_as_cell!('b'));
        wam.machine_st.heap.push(list_loc_as_cell!(5));
        wam.machine_st.heap.push(heap_loc_as_cell!(5));
        wam.machine_st.heap.push(empty_list_as_cell!());

        unify!(wam.machine_st, list_loc_as_cell!(1), heap_loc_as_cell!(0));

        assert!(!wam.machine_st.fail);

        // #2293, test7.

        wam.machine_st.heap.clear();

        wam.machine_st.heap.push(atom_as_cstr_cell!(atom!("abcde")));
        wam.machine_st.heap.push(char_as_cell!('a'));
        wam.machine_st.heap.push(list_loc_as_cell!(3));
        wam.machine_st.heap.push(heap_loc_as_cell!(3));
        wam.machine_st.heap.push(list_loc_as_cell!(5));
        wam.machine_st.heap.push(char_as_cell!('c'));
        wam.machine_st.heap.push(list_loc_as_cell!(7));
        wam.machine_st.heap.push(heap_loc_as_cell!(7));
        wam.machine_st.heap.push(list_loc_as_cell!(9));
        wam.machine_st.heap.push(char_as_cell!('e'));
        wam.machine_st.heap.push(empty_list_as_cell!());

        unify!(wam.machine_st, list_loc_as_cell!(1), heap_loc_as_cell!(0));

        assert!(!wam.machine_st.fail);
    }
}
