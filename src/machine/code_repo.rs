use crate::clause_types::*;
use crate::instructions::*;
use crate::machine::machine_indices::*;

#[derive(Debug)]
pub struct CodeRepo {
    pub(super) code: Code,
}

impl CodeRepo {
    #[inline]
    pub(super)
    fn new() -> Self {
        CodeRepo {
            code: Code::new(),
        }
    }

    #[inline]
    pub(super)
    fn lookup_local_instr<'a>(
        &'a self,
        p: LocalCodePtr,
    ) -> RefOrOwned<'a, Line> {
        match p {
            LocalCodePtr::Halt => {
                // exit with the interrupt exit code.
                std::process::exit(1);
            }
            LocalCodePtr::DirEntry(p) => {
                RefOrOwned::Borrowed(&self.code[p as usize])
            }
            LocalCodePtr::IndexingBuf(p, o, i) => {
                match &self.code[p] {
                    &Line::IndexingCode(ref indexing_lines) => {
                        match &indexing_lines[o] {
                            &IndexingLine::IndexedChoice(ref indexed_choice_instrs) => {
                                RefOrOwned::Owned(Line::IndexedChoice(indexed_choice_instrs[i]))
                            }
                            _ => {
                                unreachable!()
                            }
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                }
            }
        }
    }

    pub(super)
    fn lookup_instr<'a>(
        &'a self,
        last_call: bool,
        p: &CodePtr,
    ) -> Option<RefOrOwned<'a, Line>> {
        match p {
            &CodePtr::Local(local) => {
                return Some(self.lookup_local_instr(local));
            }
            &CodePtr::REPL(..) => {
                None
            }
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
                let call_clause = call_clause!(
                    ClauseType::CallN,
                    arity,
                    0,
                    last_call
                );

                Some(RefOrOwned::Owned(call_clause))
            }
            &CodePtr::VerifyAttrInterrupt(p) => {
                Some(RefOrOwned::Borrowed(&self.code[p]))
            }
/*
            &CodePtr::DynamicTransaction(..) => {
                None
            }
*/
        }
    }
}
