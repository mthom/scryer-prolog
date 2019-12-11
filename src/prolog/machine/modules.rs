use prolog_parser::ast::*;
use prolog_parser::tabled_rc::*;

use crate::prolog::forms::*;
use crate::prolog::machine::code_repo::*;
use crate::prolog::machine::machine_errors::*;
use crate::prolog::machine::machine_indices::*;

use std::collections::VecDeque;
use std::mem;

// Module's and related types are defined in forms.
impl Module {
    pub fn new(module_decl: ModuleDecl, atom_tbl: TabledData<Atom>) -> Self
    {
        Module {
            module_decl,
            atom_tbl,
            user_term_expansions: (Predicate::new(), VecDeque::from(vec![])),
            user_goal_expansions: (Predicate::new(), VecDeque::from(vec![])),
            term_expansions: (Predicate::new(), VecDeque::from(vec![])),
            goal_expansions: (Predicate::new(), VecDeque::from(vec![])),
            local_term_expansions: (Predicate::new(), VecDeque::from(vec![])),
            local_goal_expansions: (Predicate::new(), VecDeque::from(vec![])),
            code_dir: CodeDir::new(),
            op_dir: default_op_dir(),
            inserted_expansions: false,
            is_impromptu_module: false,
        }
    }

    pub fn dump_expansions(
        &self,
        code_repo: &mut CodeRepo,
        flags: MachineFlags,
    ) -> Result<(), ParserError> {
        {
            let te = code_repo
                .term_dir
                .entry((clause_name!("term_expansion"), 2))
                .or_insert((Predicate::new(), VecDeque::from(vec![])));

            (te.0)
                .0
                .extend((self.user_term_expansions.0).0.iter().cloned());
            te.1.extend(self.user_term_expansions.1.iter().cloned());
        }

        {
            let ge = code_repo
                .term_dir
                .entry((clause_name!("goal_expansion"), 2))
                .or_insert((Predicate::new(), VecDeque::from(vec![])));

            (ge.0)
                .0
                .extend((self.user_goal_expansions.0).0.iter().cloned());
            ge.1.extend(self.user_goal_expansions.1.iter().cloned());
        }

        code_repo.compile_hook(CompileTimeHook::TermExpansion, flags)?;
        code_repo.compile_hook(CompileTimeHook::GoalExpansion, flags)?;

        Ok(())
    }

    pub fn add_expansion_record(
        &mut self,
        hook: CompileTimeHook,
        clause: PredicateClause,
        queue: VecDeque<TopLevel>,
    ) {
        match hook {
            CompileTimeHook::TermExpansion | CompileTimeHook::UserTermExpansion => {
                (self.term_expansions.0).0.push(clause);
                self.term_expansions.1.extend(queue.into_iter());
            }
            CompileTimeHook::GoalExpansion | CompileTimeHook::UserGoalExpansion => {
                (self.goal_expansions.0).0.push(clause);
                self.goal_expansions.1.extend(queue.into_iter());
            }
        }
    }

    pub fn add_local_expansion(
        &mut self,
        hook: CompileTimeHook,
        clause: PredicateClause,
        queue: VecDeque<TopLevel>,
    ) {
        match hook {
            CompileTimeHook::TermExpansion => {
                (self.local_term_expansions.0).0.push(clause);
                self.local_term_expansions.1.extend(queue.into_iter());
            }
            CompileTimeHook::GoalExpansion => {
                (self.local_goal_expansions.0).0.push(clause);
                self.local_goal_expansions.1.extend(queue.into_iter());
            }
            _ => {}
        }
    }

    pub fn take_local_expansions(&mut self) -> Vec<(Predicate, VecDeque<TopLevel>)>
    {
        let term_expansions =
            mem::replace(&mut self.local_term_expansions, (Predicate::new(), VecDeque::new()));
        let goal_expansions =
            mem::replace(&mut self.local_goal_expansions, (Predicate::new(), VecDeque::new()));

        vec![term_expansions, goal_expansions]
    }
}

pub trait SubModuleUser {
    fn atom_tbl(&self) -> TabledData<Atom>;
    fn op_dir(&mut self) -> &mut OpDir;
    fn remove_code_index(&mut self, _: PredicateKey);
    fn get_code_index(&self, _: PredicateKey, _: ClauseName) -> Option<CodeIndex>;

    fn insert_dir_entry(&mut self, _: ClauseName, _: usize, _: CodeIndex);

    fn get_op_module_name(&mut self, name: ClauseName, fixity: Fixity) -> Option<ClauseName> {
        self.op_dir()
            .get(&(name, fixity))
            .map(|op_val| op_val.owning_module())
    }

    fn remove_module(&mut self, mod_name: ClauseName, module: &Module) {
        for export in module.module_decl.exports.iter().cloned() {
            match export {
                ModuleExport::PredicateKey((name, arity)) => {
                    let name = name.defrock_brackets();

                    match self.get_code_index((name.clone(), arity), mod_name.clone()) {
                        Some(CodeIndex(ref code_idx)) => {
                            if &code_idx.borrow().1 != &module.module_decl.name {
                                continue;
                            }

                            self.remove_code_index((name.clone(), arity));

                            // remove or respecify ops.
                            if arity == 2 {
                                if let Some(mod_name) = self.get_op_module_name(name.clone(), Fixity::In) {
                                    if mod_name == module.module_decl.name {
                                        self.op_dir().remove(&(name.clone(), Fixity::In));
                                    }
                                }
                            } else if arity == 1 {
                                if let Some(mod_name) = self.get_op_module_name(name.clone(), Fixity::Pre) {
                                    if mod_name == module.module_decl.name {
                                        self.op_dir().remove(&(name.clone(), Fixity::Pre));
                                    }
                                }

                                if let Some(mod_name) = self.get_op_module_name(name.clone(), Fixity::Post)
                                {
                                    if mod_name == module.module_decl.name {
                                        self.op_dir().remove(&(name.clone(), Fixity::Post));
                                    }
                                }
                            }
                        }                    
                        _ => {}
                    };
                },
                ModuleExport::OpDecl(op_decl) => {
                    let op_dir = self.op_dir();
                    op_dir.remove(&(op_decl.name(), op_decl.fixity()));
                }
            }
        }
    }

    // returns true on successful import.
    fn import_decl(&mut self, name: ClauseName, arity: usize, submodule: &Module) -> bool {
        let name = name.defrock_brackets();

        if let Some(code_data) = submodule.code_dir.get(&(name.clone(), arity)) {
            let name = name.with_table(submodule.atom_tbl.clone());
            let atom_tbl = self.atom_tbl();

            atom_tbl.borrow_mut().insert(name.to_rc());

            self.insert_dir_entry(name, arity, code_data.clone());
            true
        } else {
            submodule.is_impromptu_module
        }
    }

    fn use_qualified_module(
        &mut self,
        _: &mut CodeRepo,
        _: MachineFlags,
        _: &Module,
        _: &Vec<ModuleExport>,
    ) -> Result<(), SessionError>;
    
    fn use_module(
        &mut self,
        _: &mut CodeRepo,
        _: MachineFlags,
        _: &Module
    ) -> Result<(), SessionError>;
}

pub fn use_qualified_module<User>(
    user: &mut User,
    submodule: &Module,
    exports: &Vec<ModuleExport>,
) -> Result<(), SessionError>
where
    User: SubModuleUser,
{
    for export in exports.iter().cloned() {
        match export {
            ModuleExport::PredicateKey((name, arity)) => {
                if !submodule
                    .module_decl
                    .exports
                    .contains(&ModuleExport::PredicateKey((name.clone(), arity)))
                {
                    continue;
                }

                if !user.import_decl(name, arity, submodule) {
                    return Err(SessionError::ModuleDoesNotContainExport);
                }
            },
            ModuleExport::OpDecl(op_decl) => {
                if !submodule
                    .module_decl
                    .exports
                    .contains(&ModuleExport::OpDecl(op_decl.clone()))
                {
                    continue;
                }

                let op_dir = user.op_dir();
                let prec = op_decl.0;
                
                op_decl.insert_into_op_dir(
                    submodule.module_decl.name.clone(),
                    op_dir,
                    prec,
                );                   
            }
        }
    }

    Ok(())
}

pub fn use_module<User: SubModuleUser>(
    user: &mut User,
    submodule: &Module,
) -> Result<(), SessionError> {
    for export in submodule.module_decl.exports.iter().cloned() {
        match export {
            ModuleExport::PredicateKey((name, arity)) => {
                if !user.import_decl(name, arity, submodule) {
                    return Err(SessionError::ModuleDoesNotContainExport);
                }
            }
            ModuleExport::OpDecl(op_decl) => {
                let op_dir = user.op_dir();
                let prec = op_decl.0;
                
                op_decl.insert_into_op_dir(
                    submodule.module_decl.name.clone(),
                    op_dir,
                    prec,
                );                
            }
        }
    }

    Ok(())
}

impl SubModuleUser for Module {
    fn atom_tbl(&self) -> TabledData<Atom> {
        self.atom_tbl.clone()
    }

    fn op_dir(&mut self) -> &mut OpDir {
        &mut self.op_dir
    }

    fn get_code_index(&self, key: PredicateKey, _: ClauseName) -> Option<CodeIndex> {
        self.code_dir.get(&key).cloned()
    }

    fn remove_code_index(&mut self, key: PredicateKey) {
        self.code_dir.remove(&key);
    }

    fn insert_dir_entry(&mut self, name: ClauseName, arity: usize, idx: CodeIndex) {
        self.code_dir.insert((name, arity), idx);
    }

    fn use_qualified_module(
        &mut self,
        _: &mut CodeRepo,
        _: MachineFlags,
        submodule: &Module,
        exports: &Vec<ModuleExport>,
    ) -> Result<(), SessionError> {
        use_qualified_module(self, submodule, exports)?;

        (self.user_term_expansions.0)
            .0
            .extend((submodule.term_expansions.0).0.iter().cloned());
        self.user_term_expansions
            .1
            .extend(submodule.term_expansions.1.iter().cloned());

        (self.user_goal_expansions.0)
            .0
            .extend((submodule.goal_expansions.0).0.iter().cloned());
        self.user_goal_expansions
            .1
            .extend(submodule.goal_expansions.1.iter().cloned());

        Ok(())
    }

    fn use_module(
        &mut self,
        _: &mut CodeRepo,
        _: MachineFlags,
        submodule: &Module,
    ) -> Result<(), SessionError> {
        use_module(self, submodule)?;

        (self.user_term_expansions.0)
            .0
            .extend((submodule.term_expansions.0).0.iter().cloned());
        self.user_term_expansions
            .1
            .extend(submodule.term_expansions.1.iter().cloned());

        (self.user_goal_expansions.0)
            .0
            .extend((submodule.goal_expansions.0).0.iter().cloned());
        self.user_goal_expansions
            .1
            .extend(submodule.goal_expansions.1.iter().cloned());

        Ok(())
    }
}
