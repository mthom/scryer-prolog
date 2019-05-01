use prolog_parser::ast::*;

use prolog::instructions::*;
use std::collections::{HashMap, VecDeque};
use std::hash::Hash;

#[derive(Clone, Copy)]
enum IntIndex {
    External(usize), Fail, Internal(usize)
}

pub struct CodeOffsets {
    flags: MachineFlags,
    pub constants:  HashMap<Constant, ThirdLevelIndex>,
    pub lists: ThirdLevelIndex,
    pub structures: HashMap<(ClauseName, usize), ThirdLevelIndex>
}

impl CodeOffsets {
    pub fn new(flags: MachineFlags) -> Self {
        CodeOffsets {
            flags,
            constants: HashMap::new(),
            lists: Vec::new(),
            structures: HashMap::new()
        }
    }

    fn cap_choice_seq_with_trust(prelude: &mut ThirdLevelIndex) {
        prelude.last_mut().map(|instr| {
            match instr {
                &mut IndexedChoiceInstruction::Retry(i) =>
                    *instr = IndexedChoiceInstruction::Trust(i),
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

    pub fn index_term(&mut self, first_arg: &Term, index: usize)
    {
        match first_arg {
            &Term::Clause(_, ref name, ref terms, _) => {
                let code = self.structures.entry((name.clone(), terms.len()))
                               .or_insert(Vec::new());

                let is_initial_index = code.is_empty();
                code.push(Self::add_index(is_initial_index, index));
            },
            &Term::Cons(..) => {
                let is_initial_index = self.lists.is_empty();
                self.lists.push(Self::add_index(is_initial_index, index));
            },
            &Term::Constant(_, Constant::String(_))
                if !self.flags.double_quotes.is_atom() => { // strings are lists in this case.
                    let is_initial_index = self.lists.is_empty();
                    self.lists.push(Self::add_index(is_initial_index, index));
                },
            &Term::Constant(_, ref constant) => {
                let code = self.constants.entry(constant.clone())
                               .or_insert(Vec::new());

                let is_initial_index = code.is_empty();
                code.push(Self::add_index(is_initial_index, index));
            },
            _ => {}
        };
    }

    fn second_level_index<Index>(indices: HashMap<Index, ThirdLevelIndex>, prelude: &mut CodeDeque)
                                 -> HashMap<Index, IntIndex>
        where Index: Eq + Hash
    {
        let mut index_locs = HashMap::new();

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

    fn flatten_index<Index>(index: HashMap<Index, IntIndex>, len: usize)
                            -> HashMap<Index, usize>
        where Index: Eq + Hash
    {
        let mut flattened_index = HashMap::new();

        for (key, int_index) in index.into_iter() {
            match int_index {
                IntIndex::External(offset) => {
                    flattened_index.insert(key, offset + len + 1);
                },
                IntIndex::Internal(offset) => {
                    flattened_index.insert(key, offset + 1);
                },
                _ => {}
            };
        }

        flattened_index
    }

    fn adjust_internal_index(index: IntIndex) -> IntIndex
    {
        match index {
            IntIndex::Internal(o) => IntIndex::Internal(o + 1),
            IntIndex::External(o) => IntIndex::External(o),
            _ => IntIndex::Fail
        }
    }
    
    fn switch_on_constant(con_ind: HashMap<Constant, ThirdLevelIndex>, prelude: &mut CodeDeque)
                          -> IntIndex
    {
        let con_ind = Self::second_level_index(con_ind, prelude);

        if con_ind.len() > 1 {
            let index = Self::flatten_index(con_ind, prelude.len());
            let instr = IndexingInstruction::SwitchOnConstant(index.len(), index);

            prelude.push_front(Line::from(instr));

            IntIndex::Internal(1)
        } else {
            con_ind.values().next()
                   .map(|index| Self::adjust_internal_index(*index))
                   .unwrap_or(IntIndex::Fail)
        }
    }

    fn switch_on_structure(str_ind: HashMap<(ClauseName, usize), ThirdLevelIndex>,
                           prelude: &mut CodeDeque)
                           -> IntIndex
    {
        let str_ind = Self::second_level_index(str_ind, prelude);

        if str_ind.len() > 1 {
            let index = Self::flatten_index(str_ind, prelude.len());
            let instr = IndexingInstruction::SwitchOnStructure(index.len(), index);

            prelude.push_front(Line::from(instr));

            IntIndex::Internal(1)
        } else {
            str_ind.values().next()
                   .map(|index| Self::adjust_internal_index(*index))
                   .unwrap_or(IntIndex::Fail)
        }
    }

    fn switch_on_list(mut lists: ThirdLevelIndex, prelude: &mut CodeDeque) -> IntIndex
    {
        if lists.len() > 1 {
            Self::cap_choice_seq_with_trust(&mut lists);
            prelude.extend(lists.into_iter().map(|i| Line::from(i)));
            IntIndex::Internal(0)
        } else {
            lists.first()
                 .map(|i| IntIndex::External(i.offset()))
                 .unwrap_or(IntIndex::Fail)
        }
    }

    fn switch_on_str_offset_from(str_loc: IntIndex, prelude_len: usize, con_loc: IntIndex)
                                 -> usize
    {
        match str_loc {
            IntIndex::External(o) => o + prelude_len + 1,
            IntIndex::Fail => 0,
            IntIndex::Internal(_) => match con_loc {
                IntIndex::Internal(_) => 2,
                _ => 1
            }
        }
    }

    fn switch_on_con_offset_from(con_loc: IntIndex, prelude_len: usize) -> usize
    {
        match con_loc {
            IntIndex::External(offset) => offset + prelude_len + 1,
            IntIndex::Fail => 0,
            IntIndex::Internal(offset) => offset, 
        }
    }

    fn switch_on_lst_offset_from(lst_loc: IntIndex, prelude_len: usize, lst_offset: usize)
                                 -> usize
    {
        match lst_loc {
            IntIndex::External(o) => o + prelude_len + 1,
            IntIndex::Fail => 0,
            IntIndex::Internal(_) => prelude_len - lst_offset + 1
        }
    }
    
    pub fn add_indices(self, code: &mut Code, mut code_body: Code)
    {
        if self.no_indices() {
            *code = code_body;
            return;
        }

        let mut prelude = VecDeque::new();

        let lst_loc = Self::switch_on_list(self.lists, &mut prelude);
        let lst_offset = prelude.len();

        let str_loc = Self::switch_on_structure(self.structures, &mut prelude);
        let con_loc = Self::switch_on_constant(self.constants, &mut prelude);

        let prelude_length = prelude.len();

        for (index, line) in prelude.iter_mut().enumerate() {
            match line {
                  &mut Line::IndexedChoice(IndexedChoiceInstruction::Try(ref mut i))
                | &mut Line::IndexedChoice(IndexedChoiceInstruction::Retry(ref mut i))
                | &mut Line::IndexedChoice(IndexedChoiceInstruction::Trust(ref mut i)) =>
                    *i += prelude_length - index,
                _ => {}
            }
        }

        let str_loc = Self::switch_on_str_offset_from(str_loc, prelude.len(), con_loc);
        let con_loc = Self::switch_on_con_offset_from(con_loc, prelude.len());
        let lst_loc = Self::switch_on_lst_offset_from(lst_loc, prelude.len(), lst_offset);

        let switch_instr = IndexingInstruction::SwitchOnTerm(prelude.len() + 1,
                                                             con_loc,
                                                             lst_loc,
                                                             str_loc);

        prelude.push_front(Line::from(switch_instr));

        *code = Vec::from(prelude);
        code.append(&mut code_body);
    }
}
