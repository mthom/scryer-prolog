use crate::clause_types::*;
use crate::instructions::*;
use crate::machine::machine_indices::*;

#[derive(Debug)]
pub(crate) struct CodeRepo {
    pub(super) code: Code,
}

impl CodeRepo {
    #[inline]
    pub(super) fn new() -> Self {
        CodeRepo { code: Code::new() }
    }

    #[inline]
    pub(super) fn lookup_local_instr<'a>(&'a self, p: LocalCodePtr) -> RefOrOwned<'a, Line> {
        match p {
            LocalCodePtr::Halt => {
                // exit with the interrupt exit code.
                std::process::exit(1);
            }
            LocalCodePtr::DirEntry(p) => RefOrOwned::Borrowed(&self.code[p as usize]),
            LocalCodePtr::IndexingBuf(p, o, i) => match &self.code[p] {
                &Line::IndexingCode(ref indexing_lines) => match &indexing_lines[o] {
                    &IndexingLine::IndexedChoice(ref indexed_choice_instrs) => {
                        RefOrOwned::Owned(Line::IndexedChoice(indexed_choice_instrs[i]))
                    }
                    &IndexingLine::DynamicIndexedChoice(ref indexed_choice_instrs) => {
                        RefOrOwned::Owned(Line::DynamicIndexedChoice(indexed_choice_instrs[i]))
                    }
                    _ => {
                        unreachable!()
                    }
                },
                _ => {
                    unreachable!()
                }
            },
        }
    }

    pub(super) fn lookup_instr<'a>(
        &'a self,
        last_call: bool,
        p: &CodePtr,
    ) -> Option<RefOrOwned<'a, Line>> {
        match p {
            &CodePtr::Local(local) => {
                return Some(self.lookup_local_instr(local));
            }
            &CodePtr::REPL(..) => None,
            &CodePtr::BuiltInClause(ref built_in, _) => {
                let call_clause = call_clause!(
                    ClauseType::BuiltIn(built_in.clone()),
                    built_in.arity(),
                    0,
                    last_call
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

    pub(super) fn find_living_dynamic_else(
        &self,
        mut p: usize,
        cc: usize,
    ) -> Option<(usize, usize)> {
        loop {
            match &self.code[p] {
                &Line::Choice(ChoiceInstruction::DynamicElse(
                    birth,
                    death,
                    NextOrFail::Next(i),
                )) => {
                    if birth < cc && Death::Finite(cc) <= death {
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
                    if birth < cc && Death::Finite(cc) <= death {
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
                    if birth < cc && Death::Finite(cc) <= death {
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
                    if birth < cc && Death::Finite(cc) <= death {
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

    pub(super) fn find_living_dynamic(
        &self,
        p: LocalCodePtr,
        cc: usize,
    ) -> Option<(usize, usize, usize, bool)> {
        let (p, oi, mut ii) = match p {
            LocalCodePtr::IndexingBuf(p, oi, ii) => (p, oi, ii),
            _ => unreachable!(),
        };

        let indexed_choice_instrs = match &self.code[p] {
            Line::IndexingCode(ref indexing_code) => match &indexing_code[oi] {
                IndexingLine::DynamicIndexedChoice(ref indexed_choice_instrs) => {
                    indexed_choice_instrs
                }
                _ => unreachable!(),
            },
            _ => unreachable!(),
        };

        loop {
            match &indexed_choice_instrs.get(ii) {
                Some(&offset) => match &self.code[p + offset - 1] {
                    &Line::Choice(ChoiceInstruction::DynamicInternalElse(
                        birth,
                        death,
                        next_or_fail,
                    )) => {
                        if birth < cc && Death::Finite(cc) <= death {
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
