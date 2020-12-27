use crate::prolog_parser::ast::*;
use crate::prolog_parser::tabled_rc::*;

use crate::instructions::*;
use crate::rug::Integer;

use crate::indexmap::IndexMap;

use std::collections::VecDeque;
use std::convert::TryFrom;
use std::hash::Hash;
use std::rc::Rc;

#[derive(Debug, Clone, Copy)]
enum IntIndex {
    External(usize),
    Fail,
    Internal(usize),
}

#[derive(Debug)]
pub struct CodeOffsets {
    atom_tbl: TabledData<Atom>,
    pub constants: IndexMap<Constant, ThirdLevelIndex>,
    pub lists: ThirdLevelIndex,
    pub structures: IndexMap<(ClauseName, usize), ThirdLevelIndex>,
}

impl CodeOffsets {
    pub fn new() -> Self {
        CodeOffsets {
            atom_tbl: TabledData::new(Rc::new("_index".to_string())),
            constants: IndexMap::new(),
            lists: Vec::new(),
            structures: IndexMap::new(),
        }
    }

    fn cap_choice_seq_with_trust(prelude: &mut ThirdLevelIndex) {
        prelude.last_mut().map(|instr| {
            match instr {
                &mut IndexedChoiceInstruction::Retry(i) => {
                    *instr = IndexedChoiceInstruction::Trust(i)
                }
                _ => {}
            };
        });
    }

    fn add_index(is_first_index: bool, index: usize) -> IndexedChoiceInstruction {
        if is_first_index {
            IndexedChoiceInstruction::Try(index)
        } else {
            IndexedChoiceInstruction::Retry(index)
        }
    }

    fn intercept_overlapping_constant(&mut self, constant: &Constant, index: usize) {
        match constant {
            &Constant::Atom(ref name, ref op) if name.is_char() => {
                let c = name.as_str().chars().next().unwrap();
                let code = self.constants
                    .entry(Constant::Char(c))
                    .or_insert(vec![]);

                code.push(Self::add_index(code.is_empty(), index));

                if op.is_some() {
                    let code = self.constants
                        .entry(Constant::Atom(name.clone(), None))
                        .or_insert(vec![]);

                    code.push(Self::add_index(false, index));
                }
            }
            &Constant::Atom(ref name, Some(_)) => {
                let code = self.constants
                    .entry(Constant::Atom(name.clone(), None))
                    .or_insert(vec![]);

                code.push(Self::add_index(code.is_empty(), index));
            }
            &Constant::Char(c) => {
                let atom = clause_name!(c.to_string(), self.atom_tbl.clone());

                let code = self.constants
                    .entry(Constant::Atom(atom, None))
                    .or_insert(vec![]);

                code.push(Self::add_index(code.is_empty(), index));
            }
            &Constant::Fixnum(n) => {
                let code = self.constants
                    .entry(Constant::Integer(Rc::new(Integer::from(n))))
                    .or_insert(vec![]);

                code.push(Self::add_index(code.is_empty(), index));

                if n >= 0 {
                    if let Ok(n) = usize::try_from(n) {
                        let code = self.constants
                            .entry(Constant::Usize(n))
                            .or_insert(vec![]);

                        code.push(Self::add_index(code.is_empty(), index));
                    }
                }
            }
            &Constant::Integer(ref n) => {
                if let Some(n) = n.to_isize() {
                    let code = self.constants
                        .entry(Constant::Fixnum(n))
                        .or_insert(vec![]);

                    code.push(Self::add_index(code.is_empty(), index));
                }

                if let Some(n) = n.to_usize() {
                    let code = self.constants
                        .entry(Constant::Usize(n))
                        .or_insert(vec![]);

                    code.push(Self::add_index(code.is_empty(), index));
                }
            }
            &Constant::Usize(n) => {
                let code = self.constants
                    .entry(Constant::Integer(Rc::new(Integer::from(n))))
                    .or_insert(vec![]);

                code.push(Self::add_index(code.is_empty(), index));

                if let Ok(n) = isize::try_from(n) {
                    let code = self.constants
                        .entry(Constant::Fixnum(n))
                        .or_insert(vec![]);

                    code.push(Self::add_index(code.is_empty(), index));
                }
            }
            _ => {
            }
        }
    }

    pub fn index_term(&mut self, optimal_arg: &Term, index: usize) {
        match optimal_arg {
            &Term::Clause(_, ref name, ref terms, _) => {
                let code = self
                    .structures
                    .entry((name.clone(), terms.len()))
                    .or_insert(Vec::new());

                let is_initial_index = code.is_empty();
                code.push(Self::add_index(is_initial_index, index));
            }
            &Term::Cons(..) | &Term::Constant(_, Constant::String(_)) => {
                let is_initial_index = self.lists.is_empty();
                self.lists.push(Self::add_index(is_initial_index, index));
            }
            &Term::Constant(_, ref constant) => {
                self.intercept_overlapping_constant(constant, index);

                let code = self.constants
                    .entry(constant.clone())
                    .or_insert(vec![]);

                let is_initial_index = code.is_empty();
                code.push(Self::add_index(is_initial_index, index));
            }
            _ => {
            }
        };
    }

    fn second_level_index<Index>(
        indices: IndexMap<Index, ThirdLevelIndex>,
        prelude: &mut CodeDeque,
    ) -> IndexMap<Index, IntIndex>
    where
        Index: Eq + Hash,
    {
        let mut index_locs = IndexMap::new();

        for (key, mut code) in indices.into_iter() {
            if code.len() > 1 {
                index_locs.insert(key, IntIndex::Internal(prelude.len()));
                Self::cap_choice_seq_with_trust(&mut code);
                prelude.extend(code.into_iter().map(|code| Line::from(code)));
            } else {
                code.first().map(|i| {
                    index_locs.insert(key, IntIndex::External(i.offset()));
                });
            }
        }

        index_locs
    }

    fn no_indices(&self) -> bool {
        let no_constants = self.constants.is_empty();
        let no_structures = self.structures.is_empty();
        let no_lists = self.lists.is_empty();

        no_constants && no_structures && no_lists
    }

    fn flatten_index<Index>(index: IndexMap<Index, IntIndex>, len: usize) -> IndexMap<Index, usize>
    where
        Index: Eq + Hash,
    {
        let mut flattened_index = IndexMap::new();

        for (key, int_index) in index.into_iter() {
            match int_index {
                IntIndex::External(offset) => {
                    flattened_index.insert(key, offset + len + 1);
                }
                IntIndex::Internal(offset) => {
                    flattened_index.insert(key, offset + 1);
                }
                _ => {}
            };
        }

        flattened_index
    }

    fn adjust_internal_index(index: IntIndex) -> IntIndex {
        match index {
            IntIndex::Internal(o) => IntIndex::Internal(o + 1),
            IntIndex::External(o) => IntIndex::External(o),
            _ => IntIndex::Fail,
        }
    }

    fn switch_on_constant(
        con_ind: IndexMap<Constant, ThirdLevelIndex>,
        prelude: &mut CodeDeque,
        optimal_index: usize,
    ) -> IntIndex {
        let con_ind = Self::second_level_index(con_ind, prelude);

        if con_ind.len() > 1 {
            let index = Self::flatten_index(con_ind, prelude.len());
            let instr = IndexingInstruction::SwitchOnConstant(
                optimal_index,
                index.len(),
                index
            );

            prelude.push_front(Line::from(instr));

            IntIndex::Internal(1)
        } else {
            con_ind
                .values()
                .next()
                .map(|index| Self::adjust_internal_index(*index))
                .unwrap_or(IntIndex::Fail)
        }
    }

    fn switch_on_structure(
        str_ind: IndexMap<(ClauseName, usize), ThirdLevelIndex>,
        prelude: &mut CodeDeque,
        optimal_index: usize,
    ) -> IntIndex {
        let str_ind = Self::second_level_index(str_ind, prelude);

        if str_ind.len() > 1 {
            let index = Self::flatten_index(str_ind, prelude.len());
            let instr = IndexingInstruction::SwitchOnStructure(
                optimal_index,
                index.len(),
                index
            );

            prelude.push_front(Line::from(instr));

            IntIndex::Internal(1)
        } else {
            str_ind
                .values()
                .next()
                .map(|index| Self::adjust_internal_index(*index))
                .unwrap_or(IntIndex::Fail)
        }
    }

    fn switch_on_list(mut lists: ThirdLevelIndex, prelude: &mut CodeDeque) -> IntIndex {
        if lists.len() > 1 {
            Self::cap_choice_seq_with_trust(&mut lists);
            prelude.extend(lists.into_iter().map(|i| Line::from(i)));
            IntIndex::Internal(0)
        } else {
            lists
                .first()
                .map(|i| IntIndex::External(i.offset()))
                .unwrap_or(IntIndex::Fail)
        }
    }

    fn switch_on_str_offset_from(
        str_loc: IntIndex,
        prelude_len: usize,
        con_loc: IntIndex,
    ) -> usize {
        match str_loc {
            IntIndex::External(o) => o + prelude_len + 1,
            IntIndex::Fail => 0,
            IntIndex::Internal(_) => match con_loc {
                IntIndex::Internal(_) => 2,
                _ => 1,
            },
        }
    }

    fn switch_on_con_offset_from(con_loc: IntIndex, prelude_len: usize) -> usize {
        match con_loc {
            IntIndex::External(offset) => offset + prelude_len + 1,
            IntIndex::Fail => 0,
            IntIndex::Internal(offset) => offset,
        }
    }

    fn switch_on_lst_offset_from(
        lst_loc: IntIndex,
        prelude_len: usize,
    ) -> usize {
        match lst_loc {
            IntIndex::External(o) => o + prelude_len + 1,
            IntIndex::Fail => 0,
            IntIndex::Internal(_) => 1, // this internal is always 0.
        }
    }

    pub fn add_indices(self, code: &mut Code, mut code_body: Code, optimal_index: usize) {
        if self.no_indices() {
            *code = code_body;
            return;
        }

        let mut prelude = VecDeque::new();

        let lst_loc = Self::switch_on_list(self.lists, &mut prelude);
        let str_loc =
            Self::switch_on_structure(self.structures, &mut prelude, optimal_index);
        let con_loc =
            Self::switch_on_constant(self.constants, &mut prelude, optimal_index);

        let prelude_length = prelude.len();

        for (index, line) in prelude.iter_mut().enumerate() {
            match line {
                &mut Line::IndexedChoice(IndexedChoiceInstruction::Try(ref mut i)) |
                &mut Line::IndexedChoice(IndexedChoiceInstruction::Retry(ref mut i)) |
                &mut Line::IndexedChoice(IndexedChoiceInstruction::Trust(ref mut i)) => {
                    *i += prelude_length - index;
                }
                _ => {
                }
            }
        }

        let str_loc = Self::switch_on_str_offset_from(str_loc, prelude.len(), con_loc);
        let con_loc = Self::switch_on_con_offset_from(con_loc, prelude.len());
        let lst_loc = Self::switch_on_lst_offset_from(lst_loc, prelude.len());

        let switch_instr = IndexingInstruction::SwitchOnTerm(
            optimal_index,
            prelude.len() + 1,
            con_loc,
            lst_loc,
            str_loc
        );

        prelude.push_front(Line::from(switch_instr));

        *code = Vec::from(prelude);
        code.append(&mut code_body);
    }
}
