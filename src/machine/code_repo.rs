use crate::clause_types::*;
use crate::instructions::*;
use crate::machine::MachineState;
use crate::machine::machine_indices::*;

// TODO: remove this, replace with just 'Code'.
#[derive(Debug)]
pub struct CodeRepo {
    pub(super) code: Code,
}

impl CodeRepo {
    pub(super) fn lookup_instr<'a>(&'a self, machine_st: &MachineState, p: &CodePtr) -> Option<RefOrOwned<'a, Line>> {
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

                Some(RefOrOwned::Owned(call_clause))
            }
            &CodePtr::CallN(arity, _, last_call) => {
                let call_clause = call_clause!(ClauseType::CallN, arity, 0, last_call);
                Some(RefOrOwned::Owned(call_clause))
            }
            &CodePtr::VerifyAttrInterrupt(p) => Some(RefOrOwned::Borrowed(&self.code[p])),
        }
    }

    #[inline]
    pub(super) fn lookup_local_instr<'a>(&'a self, machine_st: &MachineState, p: LocalCodePtr) -> RefOrOwned<'a, Line> {
        match p {
            LocalCodePtr::Halt => {
                // exit with the interrupt exit code.
                std::process::exit(1);
            }
            LocalCodePtr::DirEntry(p) => match &self.code[p] {
                &Line::IndexingCode(ref indexing_lines) => {
                    match &indexing_lines[machine_st.oip as usize] {
                        &IndexingLine::IndexedChoice(ref indexed_choice_instrs) => {
                            RefOrOwned::Owned(Line::IndexedChoice(indexed_choice_instrs[machine_st.iip as usize]))
                        }
                        &IndexingLine::DynamicIndexedChoice(ref indexed_choice_instrs) => {
                            RefOrOwned::Owned(Line::DynamicIndexedChoice(indexed_choice_instrs[machine_st.iip as usize]))
                        }
                        _ => {
                            RefOrOwned::Borrowed(&self.code[p as usize])
                        }
                    }
                }
                _ => RefOrOwned::Borrowed(&self.code[p as usize]),
            }
        }
    }
}

impl MachineState {
    pub(super) fn find_living_dynamic_else(&self, code: &Code, mut p: usize) -> Option<(usize, usize)> {
        loop {
            match &code[p] {
                &Line::Choice(ChoiceInstruction::DynamicElse(
                    birth,
                    death,
                    NextOrFail::Next(i),
                )) => {
                    if birth < self.cc && Death::Finite(self.cc) <= death {
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
                    if birth < self.cc && Death::Finite(self.cc) <= death {
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
                    if birth < self.cc && Death::Finite(self.cc) <= death {
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
                    if birth < self.cc && Death::Finite(self.cc) <= death {
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

    pub(super) fn find_living_dynamic(&self, code: &Code, oi: u32, mut ii: u32) -> Option<(usize, u32, u32, bool)> {
        let p = self.p.local().abs_loc();

        let indexed_choice_instrs = match &code[p] {
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
                Some(&offset) => match &code[p + offset - 1] {
                    &Line::Choice(ChoiceInstruction::DynamicInternalElse(
                        birth,
                        death,
                        next_or_fail,
                    )) => {
                        if birth < self.cc && Death::Finite(self.cc) <= death {
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
