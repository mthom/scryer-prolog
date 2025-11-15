use crate::atom_table::*;

use crate::machine::heap::*;
use crate::machine::machine_errors::CycleSearchResult;
use crate::machine::system_calls::BrentAlgState;
use crate::types::*;

#[derive(Clone, Copy)]
pub struct HeapPStrIter<'a> {
    pub heap: &'a Heap,
    // pub focus: HeapCellValue,
    orig_focus: usize,
    brent_st: BrentAlgState,
    stepper: fn(&mut HeapPStrIter<'a>) -> Option<PStrIteratee>,
}

struct PStrIterStep {
    iteratee: PStrIteratee,
    next_hare: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PStrIteratee {
    Char { heap_loc: usize, value: char },
    PStrSlice { slice_loc: usize, slice_len: usize },
}

impl<'a> HeapPStrIter<'a> {
    pub fn new(heap: &'a Heap, orig_focus: usize) -> Self {
        debug_assert!(heap[orig_focus].is_ref());

        Self {
            heap,
            orig_focus,
            brent_st: BrentAlgState::new(orig_focus),
            stepper: HeapPStrIter::pre_cycle_discovery_stepper,
        }
    }

    #[inline(always)]
    pub fn focus(&self) -> usize {
        self.brent_st.hare
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

        // self.focus = self.heap[orig_hare];
        self.brent_st.hare = orig_hare;
    }

    pub fn to_string_mut(&mut self) -> String {
        let mut buf = String::with_capacity(32);

        while let Some(iteratee) = self.next() {
            match iteratee {
                PStrIteratee::Char { value: c, .. } => {
                    buf.push(c);
                }
                PStrIteratee::PStrSlice {
                    slice_loc,
                    slice_len,
                } => {
                    buf += self.heap.slice_to_str(slice_loc, slice_len);
                }
            }
        }

        buf
    }

    // return the next step in the iteration or the updated curr_hare
    // for the sake of pointing to the pstr tail
    fn step(&self, mut curr_hare: usize) -> Result<PStrIterStep, usize> {
        loop {
            read_heap_cell!(self.heap[curr_hare],
                (HeapCellValueTag::PStrLoc, h) => {
                    let HeapStringScan { string, tail_idx } = self.heap.scan_slice_to_str(h);

                    return Ok(PStrIterStep {
                        iteratee: PStrIteratee::PStrSlice { slice_loc: h, slice_len: string.len() },
                        next_hare: tail_idx,
                    });
                }
                (HeapCellValueTag::Lis, h) => {
                    let value = heap_bound_store(
                        self.heap,
                        heap_bound_deref(self.heap, self.heap[h]),
                    );

                    return value.as_char().map(|c| PStrIterStep {
                        iteratee: PStrIteratee::Char { heap_loc: curr_hare, value: c },
                        next_hare: h+1,
                    }).ok_or(curr_hare)
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
                            iteratee: PStrIteratee::Char { heap_loc: curr_hare, value: c },
                            next_hare: s+2,
                        }).ok_or(curr_hare)
                    } else {
                        Err(curr_hare)
                    };
                }
                (HeapCellValueTag::Atom, (_name, arity)) => {
                    debug_assert!(arity == 0);
                    return Err(curr_hare);
                }
                (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
                    if h == curr_hare {
                        return Err(curr_hare);
                    }

                    curr_hare = h;
                }
                _ => {
                    return Err(curr_hare);
                }
            );
        }
    }

    fn pre_cycle_discovery_stepper(&mut self) -> Option<PStrIteratee> {
        let PStrIterStep {
            iteratee,
            next_hare,
        } = match self.step(self.brent_st.hare) {
            Ok(results) => results,
            Err(next_hare) => {
                self.brent_st.hare = next_hare;
                return None;
            }
        };

        match self.brent_st.step(next_hare) {
            Some(cycle_result) => {
                debug_assert!(matches!(cycle_result, CycleSearchResult::Cyclic { .. }));

                self.walk_hare_to_cycle_end();
                self.stepper = HeapPStrIter::post_cycle_discovery_stepper;
            }
            None => {
                // self.focus = self.heap[next_hare];
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
            Ok(results) => results,
            Err(next_hare) => {
                self.brent_st.hare = next_hare;
                return None;
            }
        };

        // self.focus = self.heap[next_hare];
        self.brent_st.hare = next_hare;

        Some(iteratee)
    }

    pub(crate) fn is_cyclic(&self) -> bool {
        self.stepper as usize == Self::post_cycle_discovery_stepper as usize
    }
}

impl<'a> Iterator for HeapPStrIter<'a> {
    type Item = PStrIteratee;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        (self.stepper)(self)
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

        let pstr_cell = wam.machine_st.heap.allocate_pstr("abc ").unwrap();
        wam.machine_st
            .heap
            .push_cell(empty_list_as_cell!())
            .unwrap();

        // not overwriting anything! 0 is an interstitial cell
        // reserved for use by the runtime
        wam.machine_st.heap[0] = pstr_cell;

        {
            let mut iter = HeapPStrIter::new(&wam.machine_st.heap, 0);

            assert_eq!(
                iter.next(),
                Some(PStrIteratee::PStrSlice {
                    slice_loc: heap_index!(1),
                    slice_len: "abc ".len()
                }),
            );
            assert_eq!(iter.next(), None);
            assert!(!iter.is_cyclic());
        }

        assert_eq!(wam.machine_st.heap[2], empty_list_as_cell!());

        wam.machine_st.heap[2] = pstr_loc_as_cell!(heap_index!(3));

        wam.machine_st.heap.allocate_pstr("def").unwrap();
        let h = wam.machine_st.heap.cell_len();

        wam.machine_st.heap.push_cell(heap_loc_as_cell!(h)).unwrap();

        {
            let mut iter = HeapPStrIter::new(&wam.machine_st.heap, 0);

            assert_eq!(
                iter.next(),
                Some(PStrIteratee::PStrSlice {
                    slice_loc: heap_index!(1),
                    slice_len: "abc ".len()
                })
            );
            assert_eq!(
                iter.next(),
                Some(PStrIteratee::PStrSlice {
                    slice_loc: heap_index!(3),
                    slice_len: "def".len(),
                })
            );

            assert_eq!(iter.next(), None);
            assert!(!iter.is_cyclic());
        }

        assert_eq!(wam.machine_st.heap[h], heap_loc_as_cell!(h));

        wam.machine_st.heap[h] = empty_list_as_cell!();

        {
            let mut iter = HeapPStrIter::new(&wam.machine_st.heap, 0);

            assert_eq!(
                iter.next(),
                Some(PStrIteratee::PStrSlice {
                    slice_loc: heap_index!(1),
                    slice_len: "abc ".len()
                })
            );
            assert_eq!(
                iter.next(),
                Some(PStrIteratee::PStrSlice {
                    slice_loc: heap_index!(3),
                    slice_len: "def".len(),
                })
            );

            assert_eq!(iter.next(), None);
            assert!(!iter.is_cyclic());
        }

        wam.machine_st.heap[h] = pstr_loc_as_cell!(heap_index!(3));

        {
            let mut iter = HeapPStrIter::new(&wam.machine_st.heap, 0);
            for _ in iter.by_ref() {}
            assert!(iter.is_cyclic());
        }

        // test "abc" = [X,Y,Z].

        wam.machine_st.heap.clear();

        let pstr_cell = wam.machine_st.heap.allocate_cstr("abc").unwrap();
        let start = wam.machine_st.heap.cell_len();

        let mut writer = wam.machine_st.heap.reserve(16).unwrap();

        writer.write_with(|section| {
            section.push_cell(list_loc_as_cell!(1 + start));
            section.push_cell(heap_loc_as_cell!(1 + start));

            section.push_cell(list_loc_as_cell!(3 + start));
            section.push_cell(heap_loc_as_cell!(3 + start));

            section.push_cell(list_loc_as_cell!(5 + start));
            section.push_cell(heap_loc_as_cell!(5 + start));

            section.push_cell(empty_list_as_cell!());
        });

        unify!(wam.machine_st, pstr_cell, heap_loc_as_cell!(2));

        assert_eq!(wam.machine_st.heap[1 + start], char_as_cell!('a'));
        assert_eq!(wam.machine_st.heap[3 + start], char_as_cell!('b'));
        assert_eq!(wam.machine_st.heap[5 + start], char_as_cell!('c'));

        // test "abc" = [X,Y,Z|D].

        wam.machine_st.heap.clear();

        let pstr_cell = wam.machine_st.heap.allocate_cstr("abc").unwrap();
        let start = wam.machine_st.heap.cell_len();

        let mut writer = wam.machine_st.heap.reserve(16).unwrap();

        writer.write_with(|section| {
            section.push_cell(list_loc_as_cell!(1 + start));
            section.push_cell(heap_loc_as_cell!(1 + start)); // X

            section.push_cell(list_loc_as_cell!(3 + start));
            section.push_cell(heap_loc_as_cell!(3 + start)); // Y

            section.push_cell(list_loc_as_cell!(5 + start));
            section.push_cell(heap_loc_as_cell!(5 + start)); // Z

            section.push_cell(heap_loc_as_cell!(6 + start)); // D
        });

        unify!(wam.machine_st, pstr_cell, heap_loc_as_cell!(2));

        assert!(!wam.machine_st.fail);

        assert_eq!(wam.machine_st.heap[3], char_as_cell!('a'),);
        assert_eq!(wam.machine_st.heap[5], char_as_cell!('b'),);
        assert_eq!(wam.machine_st.heap[7], char_as_cell!('c'),);
        assert_eq!(wam.machine_st.heap[8], empty_list_as_cell!(),);

        // test "d" = [d].

        wam.machine_st.heap.clear();

        let pstr_cell = wam.machine_st.heap.allocate_cstr("d").unwrap();
        let start = wam.machine_st.heap.cell_len();

        let mut writer = wam.machine_st.heap.reserve(16).unwrap();

        writer.write_with(|section| {
            section.push_cell(list_loc_as_cell!(1 + start));
            section.push_cell(char_as_cell!('d'));
            section.push_cell(empty_list_as_cell!());
        });

        unify!(wam.machine_st, pstr_cell, heap_loc_as_cell!(start));

        assert!(!wam.machine_st.fail);

        // test "abc" = [X,b,Z].

        wam.machine_st.heap.clear();

        let pstr_cell = wam.machine_st.heap.allocate_cstr("abc").unwrap();
        let start = wam.machine_st.heap.cell_len();

        let mut writer = wam.machine_st.heap.reserve(16).unwrap();

        writer.write_with(|section| {
            section.push_cell(list_loc_as_cell!(1 + start));
            section.push_cell(heap_loc_as_cell!(1 + start));

            section.push_cell(list_loc_as_cell!(3 + start));
            section.push_cell(char_as_cell!('b'));

            section.push_cell(list_loc_as_cell!(5 + start));
            section.push_cell(heap_loc_as_cell!(5 + start));

            section.push_cell(empty_list_as_cell!());
        });

        unify!(wam.machine_st, pstr_cell, heap_loc_as_cell!(start));

        assert!(!wam.machine_st.fail);

        assert_eq!(wam.machine_st.heap[1 + start], char_as_cell!('a'));
        assert_eq!(wam.machine_st.heap[3 + start], char_as_cell!('b'));
        assert_eq!(wam.machine_st.heap[5 + start], char_as_cell!('c'));

        // test "abcdef" = [a,b,c|X].

        wam.machine_st.heap.clear();

        let pstr_cell = wam.machine_st.heap.allocate_cstr("abcdef").unwrap();
        let start = wam.machine_st.heap.cell_len();

        let mut writer = wam.machine_st.heap.reserve(16).unwrap();

        writer.write_with(|section| {
            section.push_pstr("abc");
            let h = section.cell_len(); // h == 3
            section.push_cell(heap_loc_as_cell!(h));
        });

        unify!(
            wam.machine_st,
            pstr_cell,
            pstr_loc_as_cell!(heap_index!(start))
        );

        assert!(!wam.machine_st.fail);

        assert_eq!(
            wam.machine_st.heap.slice_to_str(0, "abcdef".len()),
            "abcdef"
        );
        assert_eq!(
            wam.machine_st
                .heap
                .slice_to_str(heap_index!(start), "abc".len()),
            "abc"
        );
        assert_eq!(
            wam.machine_st.heap[3],
            pstr_loc_as_cell!(heap_index!(0) + 3)
        );

        // test iteration on X = [b,c,b,c,b,c,b,c|...] as an offset.

        wam.machine_st.heap.clear();

        wam.machine_st.heap.allocate_cstr("abc").unwrap();
        let start = wam.machine_st.heap.cell_len();

        let mut writer = wam.machine_st.heap.reserve(16).unwrap();

        writer.write_with(|section| {
            section.push_cell(pstr_loc_as_cell!('a'.len_utf8()));
        });

        {
            let mut iter = HeapPStrIter::new(&wam.machine_st.heap, start);

            assert_eq!(
                iter.next(),
                Some(PStrIteratee::PStrSlice {
                    slice_loc: 'a'.len_utf8(),
                    slice_len: "bc".len()
                })
            );

            for _ in iter {}
        }

        // #2293, test1.

        wam.machine_st.heap.clear();

        wam.machine_st.heap.allocate_cstr("a ").unwrap();
        let start = wam.machine_st.heap.cell_len();

        let mut writer = wam.machine_st.heap.reserve(16).unwrap();

        writer.write_with(|section| {
            section.push_cell(heap_loc_as_cell!(start));
            section.push_cell(list_loc_as_cell!(2 + start));
            section.push_cell(char_as_cell!(' '));
            section.push_cell(empty_list_as_cell!());
        });

        unify!(
            wam.machine_st,
            list_loc_as_cell!(start),
            pstr_loc_as_cell!(0)
        );

        assert!(!wam.machine_st.fail);

        // #2293, test2.

        wam.machine_st.heap.clear();

        wam.machine_st.heap.allocate_cstr(" a").unwrap();
        let start = wam.machine_st.heap.cell_len();

        let mut writer = wam.machine_st.heap.reserve(16).unwrap();

        writer.write_with(|section| {
            section.push_cell(char_as_cell!(' '));
            section.push_cell(list_loc_as_cell!(2 + start));
            section.push_cell(heap_loc_as_cell!(2 + start));
            section.push_cell(empty_list_as_cell!());
        });

        unify!(
            wam.machine_st,
            list_loc_as_cell!(start),
            pstr_loc_as_cell!(0)
        );

        assert_eq!(wam.machine_st.heap[2 + start], char_as_cell!('a'));
        assert!(!wam.machine_st.fail);

        // #2293, test3.

        wam.machine_st.heap.clear();

        wam.machine_st.heap.allocate_cstr("a b").unwrap();
        let start = wam.machine_st.heap.cell_len();

        let mut writer = wam.machine_st.heap.reserve(16).unwrap();

        writer.write_with(|section| {
            section.push_cell(heap_loc_as_cell!(start));
            section.push_cell(list_loc_as_cell!(2 + start));
            section.push_cell(char_as_cell!(' '));
            section.push_cell(list_loc_as_cell!(4 + start));
            section.push_cell(heap_loc_as_cell!(4 + start));
            section.push_cell(empty_list_as_cell!());
        });

        unify!(
            wam.machine_st,
            list_loc_as_cell!(start),
            pstr_loc_as_cell!(0)
        );

        assert_eq!(wam.machine_st.heap[start], char_as_cell!('a'));
        assert_eq!(wam.machine_st.heap[4 + start], char_as_cell!('b'));
        assert!(!wam.machine_st.fail);

        // #2293, test4.

        wam.machine_st.heap.clear();

        wam.machine_st.heap.allocate_cstr(" a ").unwrap();
        let start = wam.machine_st.heap.cell_len();

        let mut writer = wam.machine_st.heap.reserve(16).unwrap();

        writer.write_with(|section| {
            section.push_cell(char_as_cell!(' '));
            section.push_cell(list_loc_as_cell!(2 + start));
            section.push_cell(heap_loc_as_cell!(2 + start));
            section.push_cell(list_loc_as_cell!(4 + start));
            section.push_cell(char_as_cell!(' '));
            section.push_cell(empty_list_as_cell!());
        });

        unify!(
            wam.machine_st,
            list_loc_as_cell!(start),
            pstr_loc_as_cell!(0)
        );

        assert_eq!(wam.machine_st.heap[2 + start], char_as_cell!('a'));
        assert!(!wam.machine_st.fail);

        // #2293, test5.

        wam.machine_st.heap.clear();

        wam.machine_st.heap.allocate_cstr(" a bc").unwrap();
        let start = wam.machine_st.heap.cell_len();

        let mut writer = wam.machine_st.heap.reserve(16).unwrap();

        writer.write_with(|section| {
            section.push_cell(char_as_cell!(' '));
            section.push_cell(list_loc_as_cell!(2 + start));
            section.push_cell(heap_loc_as_cell!(2 + start));
            section.push_cell(list_loc_as_cell!(4 + start));
            section.push_cell(char_as_cell!(' '));
            section.push_cell(heap_loc_as_cell!(5 + start));
        });

        unify!(
            wam.machine_st,
            list_loc_as_cell!(start),
            pstr_loc_as_cell!(0)
        );

        assert_eq!(wam.machine_st.heap[2 + start], char_as_cell!('a'));
        assert_eq!(
            wam.machine_st.heap[5 + start],
            pstr_loc_as_cell!(heap_index!(0) + 3)
        );
        assert!(!wam.machine_st.fail);

        // #2293, test6.

        wam.machine_st.heap.clear();

        wam.machine_st.heap.allocate_cstr("abc").unwrap();
        let start = wam.machine_st.heap.cell_len();

        let mut writer = wam.machine_st.heap.reserve(16).unwrap();

        writer.write_with(|section| {
            section.push_cell(heap_loc_as_cell!(start));
            section.push_cell(list_loc_as_cell!(2 + start));
            section.push_cell(char_as_cell!('b'));
            section.push_cell(list_loc_as_cell!(4 + start));
            section.push_cell(heap_loc_as_cell!(4 + start));
            section.push_cell(empty_list_as_cell!());
        });

        unify!(
            wam.machine_st,
            list_loc_as_cell!(start),
            pstr_loc_as_cell!(0)
        );

        assert_eq!(wam.machine_st.heap[start], char_as_cell!('a'));
        assert_eq!(wam.machine_st.heap[4 + start], char_as_cell!('c'));
        assert!(!wam.machine_st.fail);

        // #2293, test7.

        wam.machine_st.heap.clear();
        wam.machine_st.heap.allocate_cstr("abcde").unwrap();

        let start = wam.machine_st.heap.cell_len();
        let mut writer = wam.machine_st.heap.reserve(16).unwrap();

        writer.write_with(|section| {
            section.push_cell(char_as_cell!('a'));
            section.push_cell(list_loc_as_cell!(2 + start));
            section.push_cell(heap_loc_as_cell!(2 + start));
            section.push_cell(list_loc_as_cell!(4 + start));
            section.push_cell(char_as_cell!('c'));
            section.push_cell(list_loc_as_cell!(6 + start));
            section.push_cell(heap_loc_as_cell!(6 + start));
            section.push_cell(list_loc_as_cell!(8 + start));
            section.push_cell(char_as_cell!('e'));
            section.push_cell(empty_list_as_cell!());
        });

        unify!(
            wam.machine_st,
            list_loc_as_cell!(start),
            pstr_loc_as_cell!(0)
        );

        assert_eq!(wam.machine_st.heap[2 + start], char_as_cell!('b'));
        assert_eq!(wam.machine_st.heap[6 + start], char_as_cell!('d'));
        assert!(!wam.machine_st.fail);
    }
}
