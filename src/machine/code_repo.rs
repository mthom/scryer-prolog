use crate::clause_types::*;
use crate::instructions::*;
use crate::machine::{Machine, MachineState};
use crate::machine::machine_indices::*;

use std::fmt;

pub(crate) enum OwnedOrIndexed {
    Indexed(usize),
    Owned(Line),
}

impl fmt::Debug for OwnedOrIndexed {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &OwnedOrIndexed::Indexed(ref index) => write!(f, "Indexed({:?})", index),
            &OwnedOrIndexed::Owned(ref owned) => write!(f, "Owned({:?})", owned),
        }
    }
}

impl OwnedOrIndexed {
    #[inline(always)]
    pub(crate) fn as_ref<'a>(&'a self, code: &'a Code) -> &'a Line {
        match self {
            &OwnedOrIndexed::Indexed(p) => &code[p],
            &OwnedOrIndexed::Owned(ref r) => r,
        }
    }
}


// TODO: remove this, replace with just 'Code'.
#[derive(Debug)]
pub struct CodeRepo {
    pub(super) code: Code,
}

impl CodeRepo {
    pub(super) fn lookup_instr(&self, machine_st: &MachineState, p: &CodePtr) -> Option<OwnedOrIndexed> {
        match p {
            &CodePtr::Local(local) => {
                return Some(self.lookup_local_instr(machine_st, local));
            }
            &CodePtr::REPL(..) => None,
            &CodePtr::BuiltInClause(ref built_in, _) => {
                let call_clause = call_clause!(
                    ClauseType::BuiltIn(built_in.clone()),
                    built_in.arity(),
                    0,
                    machine_st.last_call
                );

                Some(OwnedOrIndexed::Owned(call_clause))
            }
            &CodePtr::CallN(arity, _, last_call) => {
                let call_clause = call_clause!(ClauseType::CallN, arity, 0, last_call);
                Some(OwnedOrIndexed::Owned(call_clause))
            }
            &CodePtr::VerifyAttrInterrupt(p) => Some(OwnedOrIndexed::Indexed(p)),
        }
    }

    #[inline]
    pub(super) fn lookup_local_instr(&self, machine_st: &MachineState, p: LocalCodePtr) -> OwnedOrIndexed {
        match p {
            LocalCodePtr::Halt => {
                // exit with the interrupt exit code.
                std::process::exit(1);
            }
            LocalCodePtr::DirEntry(p) => match &self.code[p] {
                &Line::IndexingCode(ref indexing_lines) => {
                    match &indexing_lines[machine_st.oip as usize] {
                        &IndexingLine::IndexedChoice(ref indexed_choice_instrs) => {
                            OwnedOrIndexed::Owned(
                                Line::IndexedChoice(indexed_choice_instrs[machine_st.iip as usize])
                            )
                        }
                        &IndexingLine::DynamicIndexedChoice(ref indexed_choice_instrs) => {
                            OwnedOrIndexed::Owned(
                                Line::DynamicIndexedChoice(indexed_choice_instrs[machine_st.iip as usize])
                            )
                        }
                        _ => {
                            OwnedOrIndexed::Indexed(p)
                        }
                    }
                }
                _ => OwnedOrIndexed::Indexed(p)
            }
        }
    }
}

impl Machine {
    pub(super) fn find_living_dynamic_else(&self, mut p: usize) -> Option<(usize, usize)> {
        loop {
            match &self.code_repo.code[p] {
                &Line::Choice(ChoiceInstruction::DynamicElse(
                    birth,
                    death,
                    NextOrFail::Next(i),
                )) => {
                    if birth < self.machine_st.cc && Death::Finite(self.machine_st.cc) <= death {
                        return Some((p, i));
                    } else if i > 0 {
                        p += i;
                    } else {
                        return None;
                    }
                }
                &Line::Choice(ChoiceInstruction::DynamicElse(
                    birth,
                    death,
                    NextOrFail::Fail(_),
                )) => {
                    if birth < self.machine_st.cc && Death::Finite(self.machine_st.cc) <= death {
                        return Some((p, 0));
                    } else {
                        return None;
                    }
                }
                &Line::Choice(ChoiceInstruction::DynamicInternalElse(
                    birth,
                    death,
                    NextOrFail::Next(i),
                )) => {
                    if birth < self.machine_st.cc && Death::Finite(self.machine_st.cc) <= death {
                        return Some((p, i));
                    } else if i > 0 {
                        p += i;
                    } else {
                        return None;
                    }
                }
                &Line::Choice(ChoiceInstruction::DynamicInternalElse(
                    birth,
                    death,
                    NextOrFail::Fail(_),
                )) => {
                    if birth < self.machine_st.cc && Death::Finite(self.machine_st.cc) <= death {
                        return Some((p, 0));
                    } else {
                        return None;
                    }
                }
                &Line::Control(ControlInstruction::RevJmpBy(i)) => {
                    p -= i;
                }
                _ => {
                    unreachable!();
                }
            }
        }
    }

    pub(super) fn find_living_dynamic(&self, oi: u32, mut ii: u32) -> Option<(usize, u32, u32, bool)> {
        let p = self.machine_st.p.local().abs_loc();

        let indexed_choice_instrs = match &self.code_repo.code[p] {
            Line::IndexingCode(ref indexing_code) => match &indexing_code[oi as usize] {
                IndexingLine::DynamicIndexedChoice(ref indexed_choice_instrs) => {
                    indexed_choice_instrs
                }
                _ => unreachable!(),
            },
            _ => unreachable!(),
        };

        loop {
            match &indexed_choice_instrs.get(ii as usize) {
                Some(&offset) => match &self.code_repo.code[p + offset - 1] {
                    &Line::Choice(ChoiceInstruction::DynamicInternalElse(
                        birth,
                        death,
                        next_or_fail,
                    )) => {
                        if birth < self.machine_st.cc && Death::Finite(self.machine_st.cc) <= death {
                            return Some((offset, oi, ii, next_or_fail.is_next()));
                        } else {
                            ii += 1;
                        }
                    }
                    _ => unreachable!(),
                },
                None => return None,
            }
        }
    }
}

impl CodeRepo {
    #[inline]
    pub(super) fn new() -> Self {
        CodeRepo { code: Code::new() }
    }
}
