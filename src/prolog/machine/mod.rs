use prolog_parser::ast::*;
use prolog_parser::tabled_rc::*;

use prolog::instructions::*;
use prolog::compile::*;
use prolog::heap_print::*;

mod machine_errors;
pub(super) mod machine_state;

#[macro_use] mod machine_state_impl;
mod system_calls;

use prolog::machine::machine_state::*;

use std::collections::HashMap;
use std::mem::swap;
use std::ops::Index;
use std::rc::Rc;

static BUILTINS: &str = include_str!("../lib/builtins.pl");

pub struct MachineCodeIndices<'a> {
    pub(super) code_dir: &'a mut CodeDir,
    pub(super) op_dir: &'a mut OpDir,
    pub(super) modules: &'a mut ModuleDir
}

impl<'a> MachineCodeIndices<'a> {
    #[inline]
    pub(super) fn copy_and_swap(&mut self, other: &mut MachineCodeIndices<'a>) {
        *self.code_dir = other.code_dir.clone();
        *self.op_dir = other.op_dir.clone();

        swap(&mut self.code_dir, &mut other.code_dir);
        swap(&mut self.op_dir, &mut other.op_dir);
        swap(&mut self.modules, &mut other.modules);
    }

    pub(super)
    fn get_clause_type(&mut self, name: ClauseName, arity: usize, fixity: Option<Fixity>) -> ClauseType
    {
        match ClauseType::from(name, arity, fixity) {
            ClauseType::Named(name, _) => {
                let idx = self.code_dir.entry((name.clone(), arity))
                    .or_insert(CodeIndex::default());

                ClauseType::Named(name, idx.clone())
            },
            ClauseType::Op(name, fixity, _) => {
                let idx = self.code_dir.entry((name.clone(), arity))
                    .or_insert(CodeIndex::default());

                ClauseType::Op(name, fixity, idx.clone())
            },
            ct => ct
        }
    }

    #[inline]
    pub(super) fn to_code_dirs(self) -> CodeDirs<'a> {
        CodeDirs { code_dir: self.code_dir,
                   op_dir: self.op_dir,
                   modules: self.modules }
    }
}

pub struct Machine {
    ms: MachineState,
    call_policy: Box<CallPolicy>,
    cut_policy: Box<CutPolicy>,
    code: Code,
    pub(super) code_dir: CodeDir,
    pub(super) op_dir: OpDir,
    // term_dir: TermDir,
    pub(super) modules: ModuleDir,
    cached_query: Option<Code>
}

fn get_code_index(code_dir: &CodeDir, modules: &ModuleDir, key: PredicateKey, module: ClauseName)
                  -> Option<CodeIndex>
{
    match module.as_str() {
        "user" | "builtin" => code_dir.get(&key).cloned(),
        _ => modules.get(&module).and_then(|ref module| {
            module.code_dir.get(&key).cloned().map(CodeIndex::from)
        })
    }
}

impl Index<LocalCodePtr> for Machine {
    type Output = Line;

    fn index(&self, ptr: LocalCodePtr) -> &Self::Output {
        match ptr {
            LocalCodePtr::TopLevel(_, p) => {
                match &self.cached_query {
                    &Some(ref cq) => &cq[p],
                    &None => panic!("Out-of-bounds top level index.")
                }
            },
            LocalCodePtr::DirEntry(p, _) => &self.code[p]
        }
    }
}

impl<'a> SubModuleUser for MachineCodeIndices<'a> {
    fn op_dir(&mut self) -> &mut OpDir {
        self.op_dir
    }

    fn get_code_index(&self, key: PredicateKey, module: ClauseName) -> Option<CodeIndex> {
        get_code_index(&self.code_dir, &self.modules, key, module)
    }

    fn remove_code_index(&mut self, key: PredicateKey) {
        self.code_dir.remove(&key);
    }

    fn insert_dir_entry(&mut self, name: ClauseName, arity: usize, idx: ModuleCodeIndex) {
        if let Some(ref mut code_idx) = self.code_dir.get_mut(&(name.clone(), arity)) {
            if !code_idx.is_undefined() {
                println!("warning: overwriting {}/{}", &name, arity);
            }

            set_code_index!(code_idx, idx.0, idx.1);

            return;
        }

        self.code_dir.insert((name, arity), CodeIndex::from(idx));
    }
}

static LISTS: &str   = include_str!("../lib/lists.pl");
static CONTROL: &str = include_str!("../lib/control.pl");
static QUEUES: &str  = include_str!("../lib/queues.pl");

impl Machine {
    pub fn new() -> Self {
        let mut wam = Machine {
            ms: MachineState::new(),
            call_policy: Box::new(DefaultCallPolicy {}),
            cut_policy: Box::new(DefaultCutPolicy {}),
            code: Code::new(),
            code_dir: CodeDir::new(),
            op_dir: default_op_dir(),
            // term_dir: TermDir::new(),
            modules: HashMap::new(),
            cached_query: None
        };

        compile_listing(&mut wam, BUILTINS.as_bytes(),
                        default_machine_code_indices!(),
                        default_machine_code_indices!());

        compile_user_module(&mut wam, LISTS.as_bytes());
        compile_user_module(&mut wam, CONTROL.as_bytes());
        compile_user_module(&mut wam, QUEUES.as_bytes());

        wam
    }

    #[inline]
    pub fn machine_flags(&self) -> MachineFlags {
        self.ms.flags
    }

    #[inline]
    pub fn failed(&self) -> bool {
        self.ms.fail
    }

    #[inline]
    pub fn atom_tbl(&self) -> TabledData<Atom> {
        self.ms.atom_tbl.clone()
    }

    pub fn get_module(&self, name: ClauseName) -> Option<&Module> {
        self.modules.get(&name)
    }

    pub fn add_batched_code(&mut self, code: Code, code_dir: CodeDir) -> Result<(), SessionError>
    {
        for (ref key, ref idx) in code_dir.iter() {
            match ClauseType::from(key.0.clone(), key.1, None) {
                ClauseType::Named(..) | ClauseType::Op(..) => {},
                _ => {
                    // ensure we don't try to overwrite the name/arity of a builtin.
                    let err_str = format!("{}/{}", key.0, key.1);
                    return Err(SessionError::CannotOverwriteBuiltIn(err_str));
                }
            };

            if idx.module_name().as_str() == "builtins" {
                continue;
            }

            if let Some(ref existing_idx) = self.code_dir.get(&key) {
                // ensure we don't try to overwrite an existing predicate from a different module.
                if !existing_idx.is_undefined() {
                    if existing_idx.module_name() != idx.module_name() {
                        let err_str = format!("{}/{} from module {}", key.0, key.1,
                                              existing_idx.module_name().as_str());
                        return Err(SessionError::CannotOverwriteImport(err_str));
                    }
                }
            }
        }

        self.code.extend(code.into_iter());
        Ok(self.code_dir.extend(code_dir.into_iter()))
    }

    #[inline]
    pub fn add_batched_ops(&mut self, op_dir: OpDir) {
        self.op_dir.extend(op_dir.into_iter());
    }

    #[inline]
    pub fn remove_module(&mut self, module: &Module) {
        let mut indices = machine_code_indices!(&mut self.code_dir, &mut self.op_dir, &mut self.modules);
        indices.remove_module(clause_name!("user"), module);
    }

    #[inline]
    pub fn take_module(&mut self, name: ClauseName) -> Option<Module> {
        self.modules.remove(&name)
    }

    #[inline]
    pub fn insert_module(&mut self, module: Module) {
        self.modules.insert(module.module_decl.name.clone(), module);
    }
    
    #[inline]
    pub fn add_module(&mut self, module: Module, code: Code) {
        self.modules.insert(module.module_decl.name.clone(), module);
        self.code.extend(code.into_iter());
    }

    pub fn code_size(&self) -> usize {
        self.code.len()
    }

    fn cached_query_size(&self) -> usize {
        match &self.cached_query {
            &Some(ref query) => query.len(),
            _ => 0
        }
    }

    fn lookup_instr(&self, p: CodePtr) -> Option<Line> {
        match p {
            CodePtr::Local(LocalCodePtr::TopLevel(_, p)) =>
                match &self.cached_query {
                    &Some(ref cq) => Some(cq[p].clone()),
                    &None => None
                },
            CodePtr::Local(LocalCodePtr::DirEntry(p, _)) =>
                Some(self.code[p].clone()),
            CodePtr::BuiltInClause(built_in, _) =>
                Some(call_clause!(ClauseType::BuiltIn(built_in.clone()), built_in.arity(),
                                  0, self.ms.last_call)),
            CodePtr::CallN(arity, _) =>
                Some(call_clause!(ClauseType::CallN, arity, 0, self.ms.last_call))
        }
    }

    fn execute_instr(&mut self)
    {
        let instr = match self.lookup_instr(self.ms.p.clone()) {
            Some(instr) => instr,
            None => return
        };

        match instr {
            Line::Arithmetic(ref arith_instr) =>
                self.ms.execute_arith_instr(arith_instr),
            Line::Choice(ref choice_instr) =>
                self.ms.execute_choice_instr(choice_instr, &mut self.call_policy),
            Line::Cut(ref cut_instr) =>
                self.ms.execute_cut_instr(cut_instr, &mut self.cut_policy),
            Line::Control(ref control_instr) => {
                let indices = machine_code_indices!(&mut self.code_dir, &mut self.op_dir,
                                                    &mut self.modules);
//                let code_dirs = CodeDirs::new(&self.code_dir, &self.op_dir,
//                                              &self.modules);
                self.ms.execute_ctrl_instr(indices, &mut self.call_policy,
                                           &mut self.cut_policy, control_instr)
            },
            Line::Fact(ref fact) => {
                for fact_instr in fact {
                    if self.failed() {
                        break;
                    }

                    self.ms.execute_fact_instr(&fact_instr);
                }

                self.ms.p += 1;
            },
            Line::Indexing(ref indexing_instr) =>
                self.ms.execute_indexing_instr(&indexing_instr),
            Line::IndexedChoice(ref choice_instr) =>
                self.ms.execute_indexed_choice_instr(choice_instr, &mut self.call_policy),
            Line::Query(ref query) => {
                for query_instr in query {
                    if self.failed() {
                        break;
                    }

                    self.ms.execute_query_instr(&query_instr);
                }

                self.ms.p += 1;
            }
        }
    }

    fn backtrack(&mut self)
    {
        if self.ms.b > 0 {
            let b = self.ms.b - 1;

            self.ms.b0 = self.ms.or_stack[b].b0;
            self.ms.p  = self.ms.or_stack[b].bp.clone();

            if let CodePtr::Local(LocalCodePtr::TopLevel(_, p)) = self.ms.p {
                self.ms.fail = p == 0;
            } else {
                self.ms.fail = false;
            }
        } else {
            self.ms.p = CodePtr::Local(LocalCodePtr::TopLevel(0, 0));
        }
    }

    fn query_stepper<'a>(&mut self)
    {
        loop {
            self.execute_instr();

            if self.failed() {
                self.backtrack();
            }

            match self.ms.p {
                CodePtr::Local(LocalCodePtr::DirEntry(p, _)) if p < self.code.len() => {},
                CodePtr::Local(_) => break,
                _ => {}
            };
        }
    }

    fn record_var_places(&self, chunk_num: usize, alloc_locs: &AllocVarDict,
                         heap_locs: &mut HeapVarDict)
    {
        for (var, var_data) in alloc_locs {
            match var_data {
                &VarData::Perm(p) if p > 0 => {
                    let e = self.ms.e;
                    let r = var_data.as_reg_type().reg_num();
                    let addr = self.ms.and_stack[e][r].clone();

                    heap_locs.insert(var.clone(), addr);
                },
                &VarData::Temp(cn, _, _) if cn == chunk_num => {
                    let r = var_data.as_reg_type();

                    if r.reg_num() != 0 {
                        let addr = self.ms[r].clone();
                        heap_locs.insert(var.clone(), addr);
                    }
                },
                _ => {}
            }
        }
    }

    fn run_query(&mut self, alloc_locs: &AllocVarDict, heap_locs: &mut HeapVarDict)
    {
        let end_ptr = top_level_code_ptr!(0, self.cached_query_size());

        while self.ms.p < end_ptr {
            if let CodePtr::Local(LocalCodePtr::TopLevel(mut cn, p)) = self.ms.p {
                match &self[LocalCodePtr::TopLevel(cn, p)] {
                    &Line::Control(ref ctrl_instr) if ctrl_instr.is_jump_instr() => {
                        self.record_var_places(cn, alloc_locs, heap_locs);
                        cn += 1;
                    },
                    _ => {}
                }

                self.ms.p = top_level_code_ptr!(cn, p);
            }

            self.query_stepper();

            match self.ms.p {
                CodePtr::Local(LocalCodePtr::TopLevel(_, p)) if p > 0 => {},
                _ => {
                    if heap_locs.is_empty() {
                        self.record_var_places(0, alloc_locs, heap_locs);
                    }

                    break;
                }
            };
        }
    }

    fn fail(&mut self, heap_locs: &HeapVarDict) -> EvalSession
    {
        if self.ms.ball.stub.len() > 0 {
            let h = self.ms.heap.h;
            self.ms.copy_and_align_ball_to_heap();

            let error_str = self.ms.print_exception(Addr::HeapCell(h),
                                                    &heap_locs,
                                                    TermFormatter {},
                                                    PrinterOutputter::new())
                                .result();

            EvalSession::from(SessionError::QueryFailureWithException(error_str))
        } else {
            EvalSession::from(SessionError::QueryFailure)
        }
    }

    pub fn submit_query(&mut self, code: Code, alloc_locs: AllocVarDict) -> EvalSession
    {
        let mut heap_locs = HashMap::new();

        self.cached_query = Some(code);
        self.run_query(&alloc_locs, &mut heap_locs);

        if self.failed() {
            self.fail(&heap_locs)
        } else {
            EvalSession::InitialQuerySuccess(alloc_locs, heap_locs)
        }
    }

    pub fn continue_query(&mut self, alloc_l: &AllocVarDict, heap_l: &mut HeapVarDict) -> EvalSession
    {
        if !self.or_stack_is_empty() {
            let b = self.ms.b - 1;
            self.ms.p = self.ms.or_stack[b].bp.clone();

            if let CodePtr::Local(LocalCodePtr::TopLevel(_, 0)) = self.ms.p {
                return EvalSession::from(SessionError::QueryFailure);
            }

            self.run_query(alloc_l, heap_l);

            if self.failed() {
                self.fail(&heap_l)
            } else {
                EvalSession::SubsequentQuerySuccess
            }
        } else {
            EvalSession::from(SessionError::QueryFailure)
        }
    }

    pub fn heap_view<Outputter>(&self, var_dir: &HeapVarDict, mut output: Outputter) -> Outputter
       where Outputter: HCValueOutputter
    {
        let mut sorted_vars: Vec<(&Rc<Var>, &Addr)> = var_dir.iter().collect();
        sorted_vars.sort_by_key(|ref v| v.0);

        for (var, addr) in sorted_vars {
            let fmt = TermFormatter {};
            output = self.ms.print_var_eq(var.clone(), addr.clone(), var_dir, fmt, output);
        }

        output
    }

    pub fn or_stack_is_empty(&self) -> bool {
        self.ms.b == 0
    }

    pub fn clear(&mut self) {
        let mut machine = Machine::new();
        swap(self, &mut machine);
    }

    pub fn reset(&mut self) {
        self.cut_policy = Box::new(DefaultCutPolicy {});
        self.ms.reset();
    }
}
