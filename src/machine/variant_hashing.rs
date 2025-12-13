use crate::forms::*;
use crate::heap_iter::*;
use crate::types::*;
use crate::machine::*;
use crate::machine::heap::*;

use fxhash::{FxHasher, FxBuildHasher};
use hashbrown::{HashTable};

use std::hash::{Hash, Hasher};

impl MachineState {
    // determine whether two terms are variants, i.e. if there exists
    // a bijection between their variable sets such that applying it
    // to h1 produces h2 (ISO Prolog standard section 7.1.6.1).
    // return false on success and true on failure like eq_test.
    #[inline(always)]
    pub fn is_non_variant(&self, h1: HeapCellValue, h2: HeapCellValue) -> bool {
	let mut a_to_b = IndexMap::with_hasher(FxBuildHasher::default());
	let mut b_to_a = IndexMap::with_hasher(FxBuildHasher::default());

        for term_pair in ParallelHeapIter::from(self, h1, h2) {
            match term_pair {
                TermPair::Vars(v1_offset, v2_offset) => {
		    match a_to_b.entry(v1_offset) {
			indexmap::map::Entry::Occupied(stored_v2_offset) => {
			    if v2_offset != *stored_v2_offset.get() {
				return true;
			    }
			}
			indexmap::map::Entry::Vacant(entry) => {
			    entry.insert_entry(v2_offset);
			}
		    }

		    match b_to_a.entry(v2_offset) {
			indexmap::map::Entry::Occupied(stored_v1_offset) => {
			    if v1_offset != *stored_v1_offset.get() {
				return true;
			    }
			}
			indexmap::map::Entry::Vacant(entry) => {
			    entry.insert_entry(v1_offset);
			}
		    }
                }
                TermPair::Less(..) => return true,
                TermPair::Greater(..) => return true,
                TermPair::Unordered(cell_1, cell_2) if cell_1 != cell_2 => return true,
                _ => {}
            }
        }

	false
    }

    fn variant_hash(&mut self, cell: HeapCellValue) -> u64 {
	let mut var_ids = IndexMap::with_hasher(FxBuildHasher::default());
	let mut hasher = FxHasher::default();
	let mut iter = eager_stackful_preorder_iter(&mut self.heap, cell);
	let mut next_var_id = 0;

	while let Some(term) = iter.next() {
	    read_heap_cell!(term,
		(HeapCellValueTag::Str, s) => {
		    let (name, arity) = cell_as_atom_cell!(iter.heap[s]).get_name_and_arity();
		    (name.index, arity).hash(&mut hasher);
		}
	        (HeapCellValueTag::Lis) => {
		    (atom!(".").index, 2).hash(&mut hasher);
		}
		(HeapCellValueTag::PStrLoc, l) => {
		    let string = iter.heap.scan_slice_to_str(l).string;

		    for c in string.chars() {
			(atom!(".").index, 2).hash(&mut hasher);
			hasher.write_u64(AtomCell::new_char_inlined(c).get_name().index);
		    }
		}
                (HeapCellValueTag::Atom, (name, arity)) => {
		    debug_assert_eq!(arity, 0);
		    (name.index, arity).hash(&mut hasher);
		}
		(HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
		    let canonical_id = var_ids.entry(h).or_insert_with(|| {
			let id = next_var_id;
			next_var_id += 1;
			id
                    });

                    hasher.write_u64(*canonical_id);
		}
	        _ => {
		    if let Some(n) = Number::try_from((term, &self.arena.f64_tbl)).ok() {
			match n {
			    Number::Float(f) => f.hash(&mut hasher),
			    Number::Integer(n) => n.hash(&mut hasher),
			    Number::Rational(r) => r.hash(&mut hasher),
			    Number::Fixnum(f) => f.hash(&mut hasher), 
			}
		    } else {
			term.hash(&mut hasher);
		    }
		}
	    );
	}

	hasher.finish()
    }

    pub fn group_by_variant(&mut self) -> CallResult {
	let stub_gen = || functor_stub(atom!("$group_by_variant"), 2);
        let list = self.try_from_list(self.registers[1], stub_gen)?;

        let mut key_pairs = Vec::with_capacity(list.len());

        for val in list {
	    key_pairs.push(self.key_val_pair(val)?);
        }

	// the first parameter is the hash. Rust forces us to store it
	// because of non-lexical lifetime hell between
	// HashTable::find_mut and HashTable::insert_unique. also
	// avoid computing the same hash repeatedly
	let mut table: HashTable<(u64, Vec<HeapCellValue>, Vec<HeapCellValue>)> = HashTable::new();

	for (key, val) in key_pairs {
	    let hash = self.variant_hash(key);

	    match table.find_mut(hash, |(_, keys, _)| !self.is_non_variant(key, keys[0])) {
		Some((_, keys, vals)) => {
		    keys.push(key);
		    vals.push(val);
		}
		None => {
		    table.insert_unique(hash, (hash, vec![key], vec![val]), |(h, _, _)| *h);
		}
	    }
	}

	let mut list_of_lists = Vec::with_capacity(table.len());

	for (_, keys, variants) in table {
	    if let None = keys.windows(2).try_for_each(|cells| {
		unify_fn!(*self, cells[0], cells[1]);
		if self.fail { None } else { Some(()) }
	    }) {
		return Ok(());
	    }

	    let variant_list_cell = resource_error_call_result!(
		self,
		sized_iter_to_heap_list(
		    &mut self.heap,
		    variants.len(),
		    variants.into_iter(),
		)
	    );

	    let mut writer = resource_error_call_result!(self, self.heap.reserve(3));

	    let key_val_cell = writer.write_with(|section| {
		let key_val_cell = str_loc_as_cell!(section.cell_len());

		section.push_cell(atom_as_cell!(atom!("-"), 2));
		section.push_cell(keys[0]);
		section.push_cell(variant_list_cell);

		key_val_cell
	    }).result;

	    list_of_lists.push(key_val_cell);
	}

	let variant_grouped_list = resource_error_call_result!(
	    self,
	    sized_iter_to_heap_list(
		&mut self.heap,
		list_of_lists.len(),
		list_of_lists.into_iter(),
	    )
	);

	let target_addr = self.registers[2];
        unify_fn!(*self, target_addr, variant_grouped_list);
        Ok(())
    }
}


