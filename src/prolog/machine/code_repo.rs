use prolog_parser::ast::MachineFlags;

use prolog::clause_types::*;
use prolog::codegen::*;
use prolog::debray_allocator::*;
use prolog::forms::*;
use prolog::instructions::*;
use prolog::machine::compile::*;
use prolog::machine::machine_errors::*;
use prolog::machine::machine_indices::*;

use std::collections::VecDeque;

pub struct CodeRepo {
    pub(super) cached_query: Code,
    pub(super) goal_expanders: Code,
    pub(super) term_expanders: Code,
    pub(super) code: Code,
    pub(super) in_situ_code: Code,
    pub(super) term_dir: TermDir
}

impl CodeRepo {
    #[inline]
    pub(super) fn new() -> Self {
        CodeRepo {
            cached_query: vec![],
            goal_expanders: Code::new(),
            term_expanders: Code::new(),
            code: Code::new(),
            in_situ_code: Code::new(),
            term_dir: TermDir::new()
        }
    }

    #[inline]
    pub fn term_dir_entry_len(&self, key: PredicateKey) -> (usize, usize) {
        self.term_dir.get(&key)
            .map(|entry| ((entry.0).0.len(), entry.1.len()))
            .unwrap_or((0,0))
    }

    #[inline]
    pub fn truncate_terms(&mut self, key: PredicateKey, len: usize, queue_len: usize)
                          -> (Predicate, VecDeque<TopLevel>)
    {
        self.term_dir.get_mut(&key)
            .map(|entry| (Predicate((entry.0).0.drain(len ..).collect()),
                          entry.1.drain(queue_len ..).collect()))
            .unwrap_or((Predicate::new(), VecDeque::from(vec![])))
    }

    pub fn add_in_situ_result(&mut self, result: &CompiledResult, in_situ_code_dir: &mut InSituCodeDir,
                              flags: MachineFlags)
                              -> Result<(), SessionError>
    {
        let (ref decl, ref queue) = result;
        let (name, arity) = decl.0.first().and_then(|cl| {
            let arity = cl.arity();
            cl.name().map(|name| (name, arity))
        }).ok_or(SessionError::NamelessEntry)?;

        let p = self.in_situ_code.len();
        in_situ_code_dir.insert((name, arity), p);

        let mut cg = CodeGenerator::<DebrayAllocator>::new(true, flags);
        // clone the decl to avoid the need to wipe its register cells later.
        let mut decl_code = cg.compile_predicate(&decl.0.clone())?;

        compile_appendix(&mut decl_code, queue, true, flags)?;

        self.in_situ_code.extend(decl_code.into_iter());
        Ok(())
    }

    #[inline]
    pub(super)
    fn size_of_cached_query(&self) -> usize {
        self.cached_query.len()
    }

    pub(super)
    fn lookup_instr<'a>(&'a self, last_call: bool, p: &CodePtr) -> Option<RefOrOwned<'a, Line>>
    {
        match p {
            &CodePtr::Local(LocalCodePtr::UserGoalExpansion(p)) =>
                if p < self.goal_expanders.len() {
                    Some(RefOrOwned::Borrowed(&self.goal_expanders[p]))
                } else {
                    None
                },
            &CodePtr::Local(LocalCodePtr::UserTermExpansion(p)) =>
                if p < self.term_expanders.len() {
                    Some(RefOrOwned::Borrowed(&self.term_expanders[p]))
                } else {
                    None
                },
            &CodePtr::Local(LocalCodePtr::TopLevel(_, p)) =>
                if p < self.cached_query.len() {
                    Some(RefOrOwned::Borrowed(&self.cached_query[p]))
                } else {
                    None
                },
            &CodePtr::Local(LocalCodePtr::InSituDirEntry(p)) =>
                Some(RefOrOwned::Borrowed(&self.in_situ_code[p])),
            &CodePtr::Local(LocalCodePtr::DirEntry(p)) =>
                Some(RefOrOwned::Borrowed(&self.code[p])),
            &CodePtr::BuiltInClause(ref built_in, _) => {
                let call_clause = call_clause!(ClauseType::BuiltIn(built_in.clone()),
                                               built_in.arity(),
                                               0, last_call);
                Some(RefOrOwned::Owned(call_clause))
            },
            &CodePtr::CallN(arity, _) => {
                let call_clause = call_clause!(ClauseType::CallN, arity, 0, last_call);
                Some(RefOrOwned::Owned(call_clause))
            },
            &CodePtr::VerifyAttrInterrupt(p) =>
                Some(RefOrOwned::Borrowed(&self.code[p])),
            &CodePtr::DynamicTransaction(..) =>
                None
        }
    }
}
