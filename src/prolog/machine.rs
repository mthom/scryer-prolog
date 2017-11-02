use prolog::ast::*;
use prolog::builtins::*;
use prolog::codegen::*;
use prolog::copier::*;
use prolog::heapview::*;
use prolog::and_stack::*;
use prolog::or_stack::*;
use prolog::fixtures::*;

use std::collections::HashMap;
use std::ops::{Index, IndexMut};
use std::vec::Vec;

#[derive(Clone, Copy)]
enum MachineMode {
    Read,
    Write
}

struct MachineState {
    h: usize,
    s: usize,
    p: CodePtr,
    b: usize,
    b0: usize,
    e: usize,
    num_of_args: usize,
    cp: CodePtr,
    fail: bool,
    heap: Heap,
    mode: MachineMode,
    and_stack: AndStack,
    or_stack: OrStack,
    registers: Registers,
    trail: Vec<Ref>,
    tr: usize,
    hb: usize,
    block: usize, // an offset into the OR stack.
    ball: (usize, Heap) // heap boundary, and a term copy
}

struct DuplicateTerm<'a> {
    state: &'a mut MachineState
}

impl<'a> DuplicateTerm<'a> {
    fn new(state: &'a mut MachineState) -> Self {
        DuplicateTerm { state: state }
    }
}

impl<'a> Index<usize> for DuplicateTerm<'a> {
    type Output = HeapCellValue;

    fn index(&self, index: usize) -> &Self::Output {
        &self.state.heap[index]
    }
}

impl<'a> IndexMut<usize> for DuplicateTerm<'a> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.state.heap[index]
    }
}

// the ordinary, heap term copier, used by duplicate_term.
impl<'a> CopierTarget for DuplicateTerm<'a> {
    fn source(&self) -> usize {
        self.state.h
    }

    fn threshold(&self) -> usize {
        self.state.h
    }

    fn push(&mut self, hcv: HeapCellValue) {
        self.state.heap.push(hcv);
        self.state.h += 1;
    }

    fn store(&self, a: Addr) -> Addr {
        self.state.store(a)
    }

    fn deref(&self, a: Addr) -> Addr {
        self.state.deref(a)
    }

    fn stack(&mut self) -> &mut AndStack {
        &mut self.state.and_stack
    }
}

struct DuplicateBallTerm<'a> {
    state: &'a mut MachineState,
    heap_boundary: usize
}

impl<'a> DuplicateBallTerm<'a> {
    fn new(state: &'a mut MachineState) -> Self {
        let hb = state.heap.len();
        DuplicateBallTerm { state: state, heap_boundary: hb }
    }
}

impl<'a> Index<usize> for DuplicateBallTerm<'a> {
    type Output = HeapCellValue;

    fn index(&self, index: usize) -> &Self::Output {
        if index < self.heap_boundary {
            &self.state.heap[index]
        } else {
            let index = index - self.heap_boundary;
            &self.state.ball.1[index]
        }
    }
}

impl<'a> IndexMut<usize> for DuplicateBallTerm<'a> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        if index < self.heap_boundary {
            &mut self.state.heap[index]
        } else {
            let index = index - self.heap_boundary;
            &mut self.state.ball.1[index]
        }
    }
}

// the ordinary, heap term copier, used by duplicate_term.
impl<'a> CopierTarget for DuplicateBallTerm<'a> {
    fn source(&self) -> usize {
        self.heap_boundary
    }

    fn threshold(&self) -> usize {
        self.heap_boundary + self.state.ball.1.len()
    }

    fn push(&mut self, hcv: HeapCellValue) {
        self.state.ball.1.push(hcv);
    }

    fn store(&self, a: Addr) -> Addr {
        self.state.store(a)
    }

    fn deref(&self, a: Addr) -> Addr {
        self.state.deref(a)
    }

    fn stack(&mut self) -> &mut AndStack {
        &mut self.state.and_stack
    }
}

pub struct Machine {
    ms: MachineState,
    code: Code,
    code_dir: CodeDir,
    op_dir: OpDir,
    cached_query: Option<Code>
}

impl Index<RegType> for MachineState {
    type Output = Addr;

    fn index(&self, reg: RegType) -> &Self::Output {
        match reg {
            RegType::Temp(temp) => &self.registers[temp],
            RegType::Perm(perm) => {
                let e = self.e;
                &self.and_stack[e][perm]
            }
        }
    }
}

impl IndexMut<RegType> for MachineState {
    fn index_mut(&mut self, reg: RegType) -> &mut Self::Output {
        match reg {
            RegType::Temp(temp) => &mut self.registers[temp],
            RegType::Perm(perm) => {
                let e = self.e;
                &mut self.and_stack[e][perm]
            }
        }
    }
}

impl Index<CodePtr> for Machine {
    type Output = Line;

    fn index(&self, ptr: CodePtr) -> &Self::Output {
        match ptr {
            CodePtr::TopLevel(_, p) => {
                match &self.cached_query {
                    &Some(ref cq) => &cq[p],
                    &None => panic!("Out-of-bounds top level index.")
                }
            },
            CodePtr::DirEntry(p) => &self.code[p]
        }
    }
}

impl Machine {
    pub fn new() -> Self {
        let (code, code_dir, op_dir) = build_code_dir();

        Machine {
            ms: MachineState::new(),
            code: code,
            code_dir: code_dir,
            op_dir: op_dir,
            cached_query: None
        }
    }

    pub fn failed(&self) -> bool {
        self.ms.fail
    }

    fn add_user_code<'a>(&mut self, name: Atom, arity: usize, offset: usize) -> EvalSession<'a>
    {
        match self.code_dir.get(&(name.clone(), arity)) {
            Some(&(PredicateKeyType::BuiltIn, _)) =>
                return EvalSession::EntryFailure(format!("error: cannot replace built-in predicate {}/{}",
                                                         name,
                                                         arity)),
            _ => {}
        };

        self.code_dir.insert((name, arity), (PredicateKeyType::User, offset));
        EvalSession::EntrySuccess
    }

    pub fn add_fact<'a>(&mut self, fact: &Term, mut code: Code) -> EvalSession<'a>
    {
        if let Some(name) = fact.name() {
            let p = self.code.len();

            let name  = name.clone();
            let arity = fact.arity();

            self.code.append(&mut code);
            self.add_user_code(name, arity, p)
        } else {
            EvalSession::EntryFailure(format!("error: the fact has no name."))
        }
    }

    pub fn add_rule<'a>(&mut self, rule: &Rule, mut code: Code) -> EvalSession<'a>
    {
        if let Some(name) = rule.head.0.name() {
            let p = self.code.len();

            let name  = name.clone();
            let arity = rule.head.0.arity();

            self.code.append(&mut code);
            self.add_user_code(name, arity, p)
        } else {
            EvalSession::EntryFailure(format!("error: the rule has no name."))
        }
    }

    pub fn add_predicate<'a>(&mut self, clauses: &Vec<PredicateClause>, mut code: Code)
        -> EvalSession<'a>
    {
        let p = self.code.len();

        let arity = clauses.first().unwrap().arity();
        let name  = clauses.first().unwrap().name().clone();

        self.code.append(&mut code);
        self.add_user_code(name, arity, p)
    }

    fn cached_query_size(&self) -> usize {
        match &self.cached_query {
            &Some(ref query) => query.len(),
            _ => 0
        }
    }

    fn execute_instr(&mut self)
    {
        let instr = match self.ms.p {
            CodePtr::TopLevel(_, p) => {
                match &self.cached_query {
                    &Some(ref cq) => &cq[p],
                    &None => return
                }
            },
            CodePtr::DirEntry(p) => &self.code[p]
        };

        match instr {
            &Line::BuiltIn(ref built_in_instr) =>
                self.ms.execute_built_in_instr(&self.code_dir, built_in_instr),
            &Line::Choice(ref choice_instr) =>
                self.ms.execute_choice_instr(choice_instr),
            &Line::Cut(ref cut_instr) =>
                self.ms.execute_cut_instr(cut_instr),
            &Line::Control(ref control_instr) =>
                self.ms.execute_ctrl_instr(&self.code_dir, control_instr),
            &Line::Fact(ref fact) => {
                for fact_instr in fact {
                    if self.failed() {
                        break;
                    }

                    self.ms.execute_fact_instr(&fact_instr);
                }
                self.ms.p += 1;
            },
            &Line::Indexing(ref indexing_instr) =>
                self.ms.execute_indexing_instr(&indexing_instr),
            &Line::IndexedChoice(ref choice_instr) =>
                self.ms.execute_indexed_choice_instr(choice_instr),
            &Line::Query(ref query) => {
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
        let b0 = self.ms
            .or_stack
            .top()
            .map(|fr| fr.b0)
            .unwrap_or(0);

        let p = if self.ms.b > 0 {
            let b = self.ms.b - 1;
            self.ms.or_stack[b].bp
        } else {
            self.ms.p = CodePtr::TopLevel(0, 0);
            return;
        };

        self.ms.p = p;

        if let CodePtr::TopLevel(_, p) = p {
            self.ms.fail = p == 0;
            self.ms.b0 = b0;

            return;
        } else {
            self.ms.fail = false;
        }
    }

    fn query_stepper<'a>(&mut self)
    {
        loop
        {
            self.execute_instr();

            if self.failed() {
                self.backtrack();
            }

            match self.ms.p {
                CodePtr::DirEntry(p) if p < self.code.len() => {},
                _ => break
            };
        }
    }

    fn record_var_places<'a>(&self,
                             chunk_num: usize,
                             alloc_locs: &AllocVarDict<'a>,
                             heap_locs: &mut HeapVarDict<'a>)
    {
        for (var, var_data) in alloc_locs {
            match var_data {
                &VarData::Perm(_) => {
                    let e = self.ms.e;
                    let r = var_data.as_reg_type().reg_num();
                    let addr = self.ms.and_stack[e][r].clone();

                    heap_locs.insert(var, addr);
                },
                &VarData::Temp(cn, _, _) if cn == chunk_num => {
                    let r = var_data.as_reg_type();
                    let addr = self.ms[r].clone();

                    heap_locs.insert(var, addr);
                },
                _ => {}
            }
        }
    }

    fn run_query<'a>(&mut self, alloc_locs: &AllocVarDict<'a>, heap_locs: &mut HeapVarDict<'a>)
    {
        let end_ptr = CodePtr::TopLevel(0, self.cached_query_size());

        while self.ms.p < end_ptr {
            if let CodePtr::TopLevel(mut cn, p) = self.ms.p {
                if let &Line::Control(ref ctrl_instr) = &self[CodePtr::TopLevel(cn, p)] {
                    if ctrl_instr.is_jump_instr() {
                        self.record_var_places(cn, alloc_locs, heap_locs);
                        cn += 1;
                    }
                }

                self.ms.p = CodePtr::TopLevel(cn, p);
            }

            self.query_stepper();

            match self.ms.p {
                CodePtr::TopLevel(_, p) if p > 0 => {},
                _ => break
            };
        }
    }

    fn fail<'a>(&mut self) -> EvalSession<'a>
    {
        if self.ms.ball.1.len() > 0 {
            let h = self.ms.h;
            self.ms.copy_and_align_ball_to_heap();

            EvalSession::QueryFailureWithException(self.print_term(&Addr::HeapCell(h)))
        } else {
            EvalSession::QueryFailure
        }
    }

    pub fn submit_decl<'a>(&mut self, decl: &Declaration) -> EvalSession<'a> {
        match decl {
            &Declaration::Op(prec, spec, ref name) => {
                lazy_static! {
                    static ref ERR_STRING: String = String::from("an operator can't be both \
                                                                  infix and postfix.");
                }

                if is_infix!(spec) {
                    match self.op_dir.get(&(name.clone(), Fixity::Post)) {
                        Some(_) => return EvalSession::EntryFailure(ERR_STRING.clone()),
                        _ => {}
                    };
                }

                if is_postfix!(spec) {
                    match self.op_dir.get(&(name.clone(), Fixity::In)) {
                        Some(_) => return EvalSession::EntryFailure(ERR_STRING.clone()),
                        _ => {}
                    };
                }

                if prec > 0 {
                    match spec {
                        XFY | XFX | YFX => self.op_dir.insert((name.clone(), Fixity::In),
                                                              (spec, prec)),
                        XF | YF => self.op_dir.insert((name.clone(), Fixity::Post), (spec, prec)),
                        FX | FY => self.op_dir.insert((name.clone(), Fixity::Pre), (spec,prec)),
                        _ => None
                    };
                } else {
                    self.op_dir.remove(&(name.clone(), Fixity::Pre));
                    self.op_dir.remove(&(name.clone(), Fixity::In));
                    self.op_dir.remove(&(name.clone(), Fixity::Post));
                }

                EvalSession::EntrySuccess
            }
        }
    }

    pub fn submit_query<'a>(&mut self, code: Code, alloc_locs: AllocVarDict<'a>) -> EvalSession<'a>
    {
        let mut heap_locs = HashMap::new();

        self.cached_query = Some(code);
        self.run_query(&alloc_locs, &mut heap_locs);

        if self.failed() {
            self.fail()
        } else {
            EvalSession::InitialQuerySuccess(alloc_locs, heap_locs)
        }
    }

    pub fn continue_query<'a>(&mut self, alloc_locs: &AllocVarDict<'a>, heap_locs: &mut HeapVarDict<'a>)
                              -> EvalSession<'a>
    {
        if !self.or_stack_is_empty() {
            let b = self.ms.b - 1;
            self.ms.p = self.ms.or_stack[b].bp;

            if let CodePtr::TopLevel(_, 0) = self.ms.p {
                return EvalSession::QueryFailure;
            }

            self.run_query(alloc_locs, heap_locs);

            if self.failed() {
                self.fail()
            } else {
                EvalSession::SubsequentQuerySuccess
            }
        } else {
            EvalSession::QueryFailure
        }
    }

    fn print_term(&self, addr: &Addr) -> String
    {
        let mut viewer = HeapCellViewer::new(&self.ms.heap,
                                             &self.ms.and_stack,
                                             addr);

        let mut result = String::new();

        while let Some(view) = viewer.next() {
            match view {
                CellView::Con(ref r) =>
                    result += format!("{}", r).as_str(),
                CellView::HeapVar(cell_num) => {
                    result += "_";
                    result += cell_num.to_string().as_str();
                },
                CellView::StackVar(_, cell_num) => {
                        result += "s_";
                    result += cell_num.to_string().as_str();
                },
                CellView::Str(_, ref name) =>
                    result += name.as_str(),
                CellView::TToken(TToken::Bar) => {
                    match viewer.peek() {
                        Some(CellView::Con(&Constant::EmptyList)) => {
                            viewer.next();
                        },
                        Some(CellView::TToken(TToken::LSBracket(loc))) => {
                            result += ", ";

                            viewer.next();
                            viewer.remove_token(loc);
                        },
                        _ => result += " | "
                    };
                },
                CellView::TToken(token) =>
                    result += token.as_str()
            };
        }

        result
    }

    pub fn heap_view(&self, var_dir: &HeapVarDict) -> String {
        let mut result = String::new();

        for (var, addr) in var_dir {
            if result != "" {
                result += "\n\r";
            }

            result += var.as_str();
            result += " = ";

            result += self.print_term(addr).as_str();
        }

        result
    }

    pub fn or_stack_is_empty(&self) -> bool {
        self.ms.b == 0
    }

    pub fn clear(&mut self) {
        self.reset();
        self.code.clear();
        self.code_dir.clear();
    }

    pub fn reset(&mut self) {
        self.ms.reset();
    }

    pub fn op_dir(&self) -> &OpDir {
        &self.op_dir
    }
}

impl MachineState {
    fn new() -> MachineState {
        MachineState { h: 0,
                       s: 0,
                       p: CodePtr::default(),
                       b: 0,
                       b0: 0,
                       e: 0,
                       num_of_args: 0,
                       cp: CodePtr::default(),
                       fail: false,
                       heap: Vec::with_capacity(256),
                       mode: MachineMode::Write,
                       and_stack: AndStack::new(),
                       or_stack: OrStack::new(),
                       registers: vec![Addr::HeapCell(0); 64],
                       trail: Vec::new(),
                       tr: 0,
                       hb: 0,
                       block: 0,
                       ball: (0, Vec::new())
        }
    }

    fn num_frames(&self) -> usize {
        self.and_stack.len() + self.or_stack.len()
    }

    fn store(&self, a: Addr) -> Addr {
        match a {
            Addr::HeapCell(r)       => self.heap[r].as_addr(r),
            Addr::StackCell(fr, sc) => self.and_stack[fr][sc].clone(),
            addr                    => addr
        }
    }

    fn deref(&self, a: Addr) -> Addr {
        let mut a = a;

        loop {
            let value = self.store(a.clone());

            if value.is_ref() && value != a {
                a = value;
                continue;
            }

            return a;
        };
    }

    fn bind(&mut self, r1: Ref, a2: Addr) {
        let t2 = self.store(a2);

        match r1 {
            Ref::StackCell(fr, sc) =>
                self.and_stack[fr][sc] = t2,
            Ref::HeapCell(hc) =>
                self.heap[hc] = HeapCellValue::from(t2)
        };

        self.trail(r1);
    }

    fn unify(&mut self, a1: Addr, a2: Addr) {
        let mut pdl = vec![a1, a2];

        self.fail = false;

        while !(pdl.is_empty() || self.fail) {
            let d1 = self.deref(pdl.pop().unwrap());
            let d2 = self.deref(pdl.pop().unwrap());

            if d1 != d2 {
                match (self.store(d1.clone()), self.store(d2.clone())) {
                    (Addr::HeapCell(hc), _) =>
                        self.bind(Ref::HeapCell(hc), d2),
                    (_, Addr::HeapCell(hc)) =>
                        self.bind(Ref::HeapCell(hc), d1),
                    (Addr::StackCell(fr, sc), _) =>
                        self.bind(Ref::StackCell(fr, sc), d2),
                    (_, Addr::StackCell(fr, sc)) =>
                        self.bind(Ref::StackCell(fr, sc), d1),
                    (Addr::Lis(a1), Addr::Lis(a2)) => {
                        pdl.push(Addr::HeapCell(a1));
                        pdl.push(Addr::HeapCell(a2));

                        pdl.push(Addr::HeapCell(a1 + 1));
                        pdl.push(Addr::HeapCell(a2 + 1));
                    },
                    (Addr::Con(c1), Addr::Con(c2)) => {
                        if c1 != c2 {
                            self.fail = true;
                        }
                    },
                    (Addr::Str(a1), Addr::Str(a2)) => {
                        let r1 = &self.heap[a1];
                        let r2 = &self.heap[a2];

                        if let &HeapCellValue::NamedStr(n1, ref f1) = r1 {
                            if let &HeapCellValue::NamedStr(n2, ref f2) = r2 {
                                if n1 == n2 && *f1 == *f2 {
                                    for i in 1 .. n1 + 1 {
                                        pdl.push(Addr::HeapCell(a1 + i));
                                        pdl.push(Addr::HeapCell(a2 + i));
                                    }

                                    continue;
                                }
                            }
                        }

                        self.fail = true;
                    },
                    _ => self.fail = true
                };
            }
        }
    }

    fn trail(&mut self, r: Ref) {
        match r {
            Ref::HeapCell(hc) => {
                if hc < self.hb {
                    self.trail.push(r);
                    self.tr += 1;
                }
            },
            Ref::StackCell(fr, _) => {
                let fr_gi = self.and_stack[fr].global_index;
                let b_gi  = if !self.or_stack.is_empty() {
                    if self.b > 0 {
                        let b = self.b - 1;
                        self.or_stack[b].global_index
                    } else {
                        0
                    }
                } else {
                    0
                };

                if fr_gi < b_gi {
                    self.trail.push(r);
                    self.tr += 1;
                }
            }
        }
    }

    fn unwind_trail(&mut self, a1: usize, a2: usize) {
        for i in a1 .. a2 {
            match self.trail[i] {
                Ref::HeapCell(r) =>
                    self.heap[r] = HeapCellValue::Ref(Ref::HeapCell(r)),
                Ref::StackCell(fr, sc) =>
                    self.and_stack[fr][sc] = Addr::StackCell(fr, sc)
            }
        }
    }

    fn tidy_trail(&mut self) {
        if self.b == 0 {
            return;
        }

        let b = self.b - 1;
        let mut i = self.or_stack[b].tr;

        while i < self.tr {
            let tr_i = self.trail[i];
            let hb = self.hb;

            match tr_i {
                Ref::HeapCell(tr_i) =>
                    if tr_i < hb { //|| ((h < tr_i) && tr_i < b) {
                        i += 1;
                    } else {
                        let tr = self.tr;
                        let val = self.trail[tr - 1];
                        self.trail[i] = val;
                    },
                Ref::StackCell(fr, _) => {
                    let b = self.b - 1;
                    let fr_gi = self.and_stack[fr].global_index;
                    let b_gi  = if !self.or_stack.is_empty() {
                        self.or_stack[b].global_index
                    } else {
                        0
                    };

                    if fr_gi < b_gi {
                        i += 1;
                    } else {
                        let tr = self.tr;
                        let val = self.trail[tr - 1];
                        self.trail[i] = val;
                    }
                }
            };
        }
    }

    fn write_constant_to_var(&mut self, addr: Addr, c: &Constant) {
        let addr = self.deref(addr);

        match self.store(addr) {
            Addr::HeapCell(hc) => {
                self.heap[hc] = HeapCellValue::Con(c.clone());
                self.trail(Ref::HeapCell(hc));
            },
            Addr::StackCell(fr, sc) => {
                self.and_stack[fr][sc] = Addr::Con(c.clone());
                self.trail(Ref::StackCell(fr, sc));
            },
            Addr::Con(c1) => {
                if c1 != *c {
                    self.fail = true;
                }
            },
            _ => self.fail = true
        };
    }

    fn execute_fact_instr(&mut self, instr: &FactInstruction) {
        match instr {
            &FactInstruction::GetConstant(_, ref c, reg) => {
                let addr = self[reg].clone();
                self.write_constant_to_var(addr, c);
            },
            &FactInstruction::GetList(_, reg) => {
                let addr = self.deref(self[reg].clone());

                match self.store(addr.clone()) {
                    Addr::HeapCell(hc) => {
                        let h = self.h;

                        self.heap.push(HeapCellValue::Lis(h+1));
                        self.bind(Ref::HeapCell(hc), Addr::HeapCell(h));

                        self.h += 1;
                        self.mode = MachineMode::Write;
                    },
                    Addr::StackCell(fr, sc) => {
                        let h = self.h;

                        self.heap.push(HeapCellValue::Lis(h+1));
                        self.bind(Ref::StackCell(fr, sc), Addr::HeapCell(h));

                        self.h += 1;
                        self.mode = MachineMode::Write;
                    },
                    Addr::Lis(a) => {
                        self.s = a;
                        self.mode = MachineMode::Read;
                    },
                    _ => self.fail = true
                };
            },
            &FactInstruction::GetStructure(_, ref name, arity, reg) => {
                let addr = self.deref(self[reg].clone());

                match self.store(addr.clone()) {
                    Addr::Str(a) => {
                        let result = &self.heap[a];

                        if let &HeapCellValue::NamedStr(narity, ref str) = result {
                            if narity == arity && *name == *str {
                                self.s = a + 1;
                                self.mode = MachineMode::Read;
                            } else {
                                self.fail = true;
                            }
                        }
                    },
                    Addr::HeapCell(_) | Addr::StackCell(_, _) => {
                        self.heap.push(HeapCellValue::Str(self.h + 1));
                        self.heap.push(HeapCellValue::NamedStr(arity, name.clone()));

                        let h = self.h;

                        self.bind(addr.as_ref().unwrap(), Addr::HeapCell(h));

                        self.h += 2;
                        self.mode = MachineMode::Write;
                    },
                    _ => self.fail = true
                };
            },
            &FactInstruction::GetVariable(norm, arg) =>
                self[norm] = self.registers[arg].clone(),
            &FactInstruction::GetValue(norm, arg) => {
                let norm_addr = self[norm].clone();
                let reg_addr  = self.registers[arg].clone();

                self.unify(norm_addr, reg_addr);
            },
            &FactInstruction::UnifyConstant(ref c) => {
                match self.mode {
                    MachineMode::Read  => {
                        let addr = Addr::HeapCell(self.s);
                        self.write_constant_to_var(addr, c);
                    },
                    MachineMode::Write => {
                        self.heap.push(HeapCellValue::Con(c.clone()));
                        self.h += 1;
                    }
                };

                self.s += 1;
            },
            &FactInstruction::UnifyVariable(reg) => {
                match self.mode {
                    MachineMode::Read  =>
                        self[reg] = self.heap[self.s].as_addr(self.s),
                    MachineMode::Write => {
                        let h = self.h;

                        self.heap.push(HeapCellValue::Ref(Ref::HeapCell(h)));
                        self[reg] = Addr::HeapCell(self.h);
                        self.h += 1;
                    }
                };

                self.s += 1;
            },
            &FactInstruction::UnifyLocalValue(reg) => {
                let s = self.s;

                match self.mode {
                    MachineMode::Read  => {
                        let reg_addr = self[reg].clone();
                        self.unify(reg_addr, Addr::HeapCell(s));
                    },
                    MachineMode::Write => {
                        let addr = self.deref(self[reg].clone());
                        let h    = self.h;

                        if let Addr::HeapCell(hc) = addr {
                            if hc < h {
                                let val = self.heap[hc].clone();
                                self.heap.push(val);

                                self.h += 1;
                                self.s += 1;

                                return;
                            }
                        }

                        self.heap.push(HeapCellValue::Ref(Ref::HeapCell(h)));
                        self.bind(Ref::HeapCell(h), addr);

                        self.h += 1;
                    }
                };

                self.s += 1;
            },
            &FactInstruction::UnifyValue(reg) => {
                let s = self.s;

                match self.mode {
                    MachineMode::Read  => {
                        let reg_addr = self[reg].clone();
                        self.unify(reg_addr, Addr::HeapCell(s));
                    },
                    MachineMode::Write => {
                        let heap_val = self.store(self[reg].clone());
                        self.heap.push(HeapCellValue::from(heap_val));
                        self.h += 1;
                    }
                };

                self.s += 1;
            },
            &FactInstruction::UnifyVoid(n) => {
                match self.mode {
                    MachineMode::Read =>
                        self.s += n,
                    MachineMode::Write => {
                        let h = self.h;

                        for i in h .. h + n {
                            self.heap.push(HeapCellValue::Ref(Ref::HeapCell(i)));
                        }

                        self.h += n;
                    }
                };
            }
        };
    }

    fn execute_indexing_instr(&mut self, instr: &IndexingInstruction) {
        match instr {
            &IndexingInstruction::SwitchOnTerm(v, c, l, s) => {
                let a1 = self.registers[1].clone();
                let addr = self.store(self.deref(a1));

                let offset = match addr {
                    Addr::HeapCell(_) | Addr::StackCell(_, _) => v,
                    Addr::Con(_) => c,
                    Addr::Lis(_) => l,
                    Addr::Str(_) => s
                };

                match offset {
                    0 => self.fail = true,
                    o => self.p += o
                };
            },
            &IndexingInstruction::SwitchOnConstant(_, ref hm) => {
                let a1 = self.registers[1].clone();
                let addr = self.store(self.deref(a1));

                let offset = match addr {
                    Addr::Con(constant) => {
                        match hm.get(&constant) {
                            Some(offset) => *offset,
                            _ => 0
                        }
                    },
                    _ => 0
                };

                match offset {
                    0 => self.fail = true,
                    o => self.p += o,
                };
            },
            &IndexingInstruction::SwitchOnStructure(_, ref hm) => {
                let a1 = self.registers[1].clone();
                let addr = self.store(self.deref(a1));

                let offset = match addr {
                    Addr::Str(s) => {
                        if let &HeapCellValue::NamedStr(arity, ref name) = &self.heap[s] {
                            match hm.get(&(name.clone(), arity)) {
                                Some(offset) => *offset,
                                _ => 0
                            }
                        } else {
                            0
                        }
                    },
                    _ => 0
                };

                match offset {
                    0 => self.fail = true,
                    o => self.p += o
                };
            }
        };
    }

    fn execute_query_instr(&mut self, instr: &QueryInstruction) {
        match instr {
            &QueryInstruction::GetVariable(norm, arg) =>
                self[norm] = self.registers[arg].clone(),
            &QueryInstruction::PutConstant(_, ref constant, reg) =>
                self[reg] = Addr::Con(constant.clone()),
            &QueryInstruction::PutList(_, reg) =>
                self[reg] = Addr::Lis(self.h),
            &QueryInstruction::PutStructure(_, ref name, arity, reg) => {
                self.heap.push(HeapCellValue::NamedStr(arity, name.clone()));
                self[reg] = Addr::Str(self.h);
                self.h += 1;
            },
            &QueryInstruction::PutUnsafeValue(n, arg) => {
                let e    = self.e;
                let addr = self.deref(Addr::StackCell(e, n));

                if addr.is_protected(e) {
                    self.registers[arg] = self.store(addr);
                } else {
                    let h = self.h;

                    self.heap.push(HeapCellValue::Ref(Ref::HeapCell(h)));
                    self.bind(Ref::HeapCell(h), addr);

                    self.registers[arg] = self.heap[h].as_addr(h);
                    self.h += 1;
                }
            },
            &QueryInstruction::PutValue(norm, arg) =>
                self.registers[arg] = self[norm].clone(),
            &QueryInstruction::PutVariable(norm, arg) => {
                match norm {
                    RegType::Perm(n) => {
                        let e = self.e;

                        self[norm] = Addr::StackCell(e, n);
                        self.registers[arg] = self[norm].clone();
                    },
                    RegType::Temp(_) => {
                        let h = self.h;
                        self.heap.push(HeapCellValue::Ref(Ref::HeapCell(h)));

                        self[norm] = Addr::HeapCell(h);
                        self.registers[arg] = Addr::HeapCell(h);

                        self.h += 1;
                    }
                };
            },
            &QueryInstruction::SetConstant(ref constant) => {
                self.heap.push(HeapCellValue::Con(constant.clone()));
                self.h += 1;
            },
            &QueryInstruction::SetLocalValue(reg) => {
                let addr = self.deref(self[reg].clone());
                let h    = self.h;

                if let Addr::HeapCell(hc) = addr {
                    if hc < h {
                        self.heap.push(HeapCellValue::from(addr));
                        self.h += 1;
                        return;
                    }
                }

                self.heap.push(HeapCellValue::Ref(Ref::HeapCell(h)));
                self.bind(Ref::HeapCell(h), addr);

                self.h += 1;
            },
            &QueryInstruction::SetVariable(reg) => {
                let h = self.h;
                self.heap.push(HeapCellValue::Ref(Ref::HeapCell(h)));
                self[reg] = Addr::HeapCell(h);

                self.h += 1;
            },
            &QueryInstruction::SetValue(reg) => {
                let heap_val = self[reg].clone();
                self.heap.push(HeapCellValue::from(heap_val));

                self.h += 1;
            },
            &QueryInstruction::SetVoid(n) => {
                let h = self.h;

                for i in h .. h + n {
                    self.heap.push(HeapCellValue::Ref(Ref::HeapCell(i)));
                }

                self.h += n;
            }
        }
    }

    fn try_call_predicate(&mut self, code_dir: &CodeDir, name: Atom, arity: usize)
    {
        let compiled_tl_index = code_dir.get(&(name, arity)).map(|index| index.1);

        match compiled_tl_index {
            Some(compiled_tl_index) => {
                self.cp = self.p + 1;
                self.num_of_args = arity;
                self.b0 = self.b;
                self.p  = CodePtr::DirEntry(compiled_tl_index);
            },
            None => self.fail = true
        };
    }

    fn try_execute_predicate(&mut self, code_dir: &CodeDir, name: Atom, arity: usize)
    {
        let compiled_tl_index = code_dir.get(&(name, arity)).map(|index| index.1);

        match compiled_tl_index {
            Some(compiled_tl_index) => {
                self.num_of_args = arity;
                self.b0 = self.b;
                self.p  = CodePtr::DirEntry(compiled_tl_index);
            },
            None => self.fail = true
        };
    }

    fn handle_internal_call_n(&mut self, code_dir: &CodeDir)
    {
        let arity = self.num_of_args + 1;
        let pred  = self.registers[1].clone();

        for i in 2 .. arity {
            self.registers[i-1] = self.registers[i].clone();
        }

        if arity > 1 {
            self.registers[arity - 1] = pred;

            if let Some((name, arity)) = self.setup_call_n(arity - 1) {
                self.try_execute_predicate(code_dir, name, arity);
            }
        } else {
            self.fail = true;
        }
    }

    fn goto_throw(&mut self) {
        self.num_of_args = 1;
        self.b0 = self.b;
        self.p  = CodePtr::DirEntry(59);
    }

    fn throw_exception(&mut self, mut hcv: Vec<HeapCellValue>) {
        let h = self.h;

        self.registers[1] = Addr::HeapCell(h);
        self.h += hcv.len();

        self.heap.append(&mut hcv);
        self.goto_throw();
    }

    fn setup_call_n(&mut self, arity: usize) -> Option<PredicateKey>
    {
        let addr = self.store(self.deref(self.registers[arity].clone()));

        let (name, narity) = match addr {
            Addr::Str(a) => {
                let result = self.heap[a].clone();

                if let HeapCellValue::NamedStr(narity, name) = result {
                    if narity + arity > 63 {
                        self.throw_exception(functor!("representation_error",
                                                      1,
                                                      [atom!("exceeds_max_arity")]));
                        return None;
                    }

                    for i in (1 .. arity).rev() {
                        self.registers[i + narity] = self.registers[i].clone();
                    }

                    for i in 1 .. narity + 1 {
                        self.registers[i] = self.heap[a + i].as_addr(a + i);
                    }

                    (name, narity)
                } else {
                    self.fail = true;
                    return None;
                }
            },
            Addr::Con(Constant::Atom(name)) => (name, 0),
            Addr::HeapCell(_) | Addr::StackCell(_, _) => {
                self.throw_exception(functor!("instantiation_error", 0, []));
                return None;
            },
            _ => {
                self.throw_exception(functor!("type_error",
                                              2,
                                              [atom!("callable"),
                                               HeapCellValue::from(addr)]));
                return None;
            }
        };

        Some((name, arity + narity - 1))
    }

    fn copy_and_align_ball_to_heap(&mut self) {
        let diff = self.ball.0 - self.h;

        for heap_value in self.ball.1.iter().cloned() {
            self.heap.push(match heap_value {
                HeapCellValue::Con(c) => HeapCellValue::Con(c),
                HeapCellValue::Lis(a) => HeapCellValue::Lis(a - diff),
                HeapCellValue::Ref(Ref::HeapCell(hc)) =>
                    HeapCellValue::Ref(Ref::HeapCell(hc - diff)),
                HeapCellValue::Str(s) => HeapCellValue::Str(s - diff),
                _ => heap_value
            });
        }

        self.h += self.ball.1.len();
    }

    fn execute_built_in_instr(&mut self, code_dir: &CodeDir, instr: &BuiltInInstruction)
    {
        match instr {
            &BuiltInInstruction::DuplicateTerm => {
                let old_h = self.h;

                let a1 = self[temp_v!(1)].clone();
                let a2 = self[temp_v!(2)].clone();

                // drop the mutable references contained in gadget
                // once the term has been duplicated.
                {
                    let mut gadget = DuplicateTerm::new(self);
                    gadget.duplicate_term(a1);
                }

                self.unify(Addr::HeapCell(old_h), a2);

                self.p += 1;
            },
            &BuiltInInstruction::GetCurrentBlock => {
                let c = Constant::Usize(self.block);
                let addr = self[temp_v!(1)].clone();

                self.write_constant_to_var(addr, &c);
                self.p += 1;
            },
            &BuiltInInstruction::Unify => {
                let a1 = self[temp_v!(1)].clone();
                let a2 = self[temp_v!(2)].clone();

                self.unify(a1, a2);
                self.p += 1;
            },
            &BuiltInInstruction::EraseBall => {
                self.ball.0 = 0;
                self.ball.1.truncate(0);
                self.p += 1;
            },
            &BuiltInInstruction::GetBall => {
                let addr = self.store(self.deref(self[temp_v!(1)].clone()));
                let h = self.h;

                if self.ball.1.len() > 0 {
                    self.copy_and_align_ball_to_heap();
                } else {
                    self.fail = true;
                    return;
                }

                let ball = self.heap[h].as_addr(h);

                match addr.as_ref() {
                    Some(r) => {
                        self.bind(r, ball);
                        self.p += 1;
                    },
                    _ => self.fail = true
                };
            },
            &BuiltInInstruction::SetBall => {
                let addr = self[temp_v!(1)].clone();
                self.ball.0 = self.h;

                {
                    let mut duplicator = DuplicateBallTerm::new(self);
                    duplicator.duplicate_term(addr);
                }

                self.p += 1;
            },
            &BuiltInInstruction::CleanUpBlock => {
                let nb = self.store(self.deref(self[temp_v!(1)].clone()));

                match nb {
                    Addr::Con(Constant::Usize(nb)) => {
                        let b = self.b - 1;

                        if nb > 0 && self.or_stack[b].b == nb {
                            self.b = self.or_stack[nb - 1].b;
                        }

                        self.p += 1;
                    },
                    _ => self.fail = true
                };
            },
            &BuiltInInstruction::InstallNewBlock => {
                self.block = self.b;
                let c = Constant::Usize(self.block);
                let addr = self[temp_v!(1)].clone();

                self.write_constant_to_var(addr, &c);
                self.p += 1;
            },
            &BuiltInInstruction::ResetBlock => {
                let addr = self.deref(self[temp_v!(1)].clone());

                match self.store(addr) {
                    Addr::Con(Constant::Usize(b)) => {
                        self.block = b;
                        self.p += 1;
                    },
                    _ => self.fail = true
                };
            },
            &BuiltInInstruction::UnwindStack => {
                self.b = self.block;
                self.fail = true;
            },
            &BuiltInInstruction::IsAtomic => {
                let d = self.deref(self[temp_v!(1)].clone());

                match d {
                    Addr::Con(_) => self.p += 1,
                    _ => self.fail = true
                };
            },
            &BuiltInInstruction::IsVar => {
                let d = self.deref(self[temp_v!(1)].clone());

                match d {
                    Addr::HeapCell(_) | Addr::StackCell(_,_) =>
                        self.p += 1,
                    _ => self.fail = true
                };
            },
            &BuiltInInstruction::InternalCallN =>
                self.handle_internal_call_n(code_dir),
            &BuiltInInstruction::Fail => {
                self.fail = true;
                self.p += 1;
            }
        };
    }

    fn execute_ctrl_instr(&mut self, code_dir: &CodeDir, instr: &ControlInstruction)
    {
        match instr {
            &ControlInstruction::Allocate(num_cells) => {
                let num_frames = self.num_frames();

                self.and_stack.push(num_frames + 1, self.e, self.cp, num_cells);

                self.e = self.and_stack.len() - 1;
                self.p += 1;
            },
            &ControlInstruction::Call(ref name, arity, _) =>
                self.try_call_predicate(code_dir, name.clone(), arity),
            &ControlInstruction::CatchCall => {
                self.cp = self.p + 1;
                self.num_of_args = 3;
                self.b0 = self.b;
                self.p  = CodePtr::DirEntry(5);
            },
            &ControlInstruction::CatchExecute => {
                self.num_of_args = 3;
                self.b0 = self.b;
                self.p  = CodePtr::DirEntry(5);
            },
            &ControlInstruction::CallN(arity) =>
                if let Some((name, arity)) = self.setup_call_n(arity) {
                    self.try_call_predicate(code_dir, name, arity);
                },
            &ControlInstruction::Deallocate => {
                let e = self.e;

                self.cp = self.and_stack[e].cp;
                self.e  = self.and_stack[e].e;

                self.p += 1;
            },
            &ControlInstruction::Execute(ref name, arity) =>
                self.try_execute_predicate(code_dir, name.clone(), arity),
            &ControlInstruction::ExecuteN(arity) =>
                if let Some((name, arity)) = self.setup_call_n(arity) {
                    self.try_execute_predicate(code_dir, name, arity);
                },
            &ControlInstruction::Goto(p, arity) => {
                self.num_of_args = arity;
                self.b0 = self.b;
                self.p  = CodePtr::DirEntry(p);
            },
            &ControlInstruction::Proceed =>
                self.p = self.cp,
            &ControlInstruction::ThrowCall => {
                self.cp = self.p + 1;
                self.goto_throw();
            },
            &ControlInstruction::ThrowExecute => {
                self.goto_throw();
            }
        };
    }

    fn execute_indexed_choice_instr(&mut self, instr: &IndexedChoiceInstruction)
    {
        match instr {
            &IndexedChoiceInstruction::Try(l) => {
                let n = self.num_of_args;
                let num_frames = self.num_frames();

                self.or_stack.push(num_frames + 1,
                                   self.e,
                                   self.cp,
                                   self.b,
                                   self.p + 1,
                                   self.tr,
                                   self.h,
                                   self.b0,
                                   self.num_of_args);

                self.b = self.or_stack.len();
                let b = self.b - 1;

                for i in 1 .. n + 1 {
                    self.or_stack[b][i] = self.registers[i].clone();
                }

                self.hb = self.h;
                self.p += l;
            },
            &IndexedChoiceInstruction::Retry(l) => {
                let b = self.b - 1;
                let n = self.or_stack[b].num_args();

                for i in 1 .. n + 1 {
                    self.registers[i] = self.or_stack[b][i].clone();
                }

                self.e = self.or_stack[b].e;
                self.cp = self.or_stack[b].cp;

                self.or_stack[b].bp = self.p + 1;

                let old_tr  = self.or_stack[b].tr;
                let curr_tr = self.tr;

                self.unwind_trail(old_tr, curr_tr);
                self.tr = self.or_stack[b].tr;

                self.trail.truncate(self.tr);
                self.heap.truncate(self.or_stack[b].h);

                self.h  = self.or_stack[b].h;
                self.hb = self.h;

                self.p += l;
            },
            &IndexedChoiceInstruction::Trust(l) => {
                let b = self.b - 1;
                let n = self.or_stack[b].num_args();

                for i in 1 .. n + 1 {
                    self.registers[i] = self.or_stack[b][i].clone();
                }

                self.e  = self.or_stack[b].e;
                self.cp = self.or_stack[b].cp;

                let old_tr  = self.or_stack[b].tr;
                let curr_tr = self.tr;

                self.unwind_trail(old_tr, curr_tr);

                self.tr = self.or_stack[b].tr;
                self.trail.truncate(self.tr);

                self.h = self.or_stack[b].h;
                self.heap.truncate(self.h);

                self.b = self.or_stack[b].b;

                self.or_stack.pop();

                self.hb = self.h;
                self.p += l;
            }
        };
    }

    fn execute_choice_instr(&mut self, instr: &ChoiceInstruction)
    {
        match instr {
            &ChoiceInstruction::TryMeElse(offset) => {
                let n = self.num_of_args;
                let num_frames = self.num_frames();

                self.or_stack.push(num_frames + 1,
                                   self.e,
                                   self.cp,
                                   self.b,
                                   self.p + offset,
                                   self.tr,
                                   self.h,
                                   self.b0,
                                   self.num_of_args);

                self.b = self.or_stack.len();
                let b  = self.b - 1;

                for i in 1 .. n + 1 {
                    self.or_stack[b][i] = self.registers[i].clone();
                }

                self.hb = self.h;
                self.p += 1;
            },
            &ChoiceInstruction::RetryMeElse(offset) => {
                let b = self.b - 1;
                let n = self.or_stack[b].num_args();

                for i in 1 .. n + 1 {
                    self.registers[i] = self.or_stack[b][i].clone();
                }

                self.e = self.or_stack[b].e;
                self.cp = self.or_stack[b].cp;

                self.or_stack[b].bp = self.p + offset;

                let old_tr  = self.or_stack[b].tr;
                let curr_tr = self.tr;

                self.unwind_trail(old_tr, curr_tr);
                self.tr = self.or_stack[b].tr;

                self.trail.truncate(self.tr);
                self.heap.truncate(self.or_stack[b].h);

                self.h  = self.or_stack[b].h;
                self.hb = self.h;

                self.p += 1;
            },
            &ChoiceInstruction::TrustMe => {
                let b = self.b - 1;
                let n = self.or_stack[b].num_args();

                for i in 1 .. n + 1 {
                    self.registers[i] = self.or_stack[b][i].clone();
                }

                self.e  = self.or_stack[b].e;
                self.cp = self.or_stack[b].cp;

                let old_tr  = self.or_stack[b].tr;
                let curr_tr = self.tr;

                self.unwind_trail(old_tr, curr_tr);

                self.tr = self.or_stack[b].tr;
                self.trail.truncate(self.tr);

                self.h = self.or_stack[b].h;
                self.heap.truncate(self.h);

                self.b = self.or_stack[b].b;

                self.or_stack.pop();

                self.hb = self.h;
                self.p += 1;
            }
        }
    }

    fn execute_cut_instr(&mut self, instr: &CutInstruction) {
        match instr {
            &CutInstruction::Cut(ref term) => {
                let b = self.b;
                let e = self.e;
                let b0 = self.and_stack[e].b0; // STACK[E+2+1]

                if b > b0 {
                    self.b = b0;
                    self.tidy_trail();
                }

                if let &Terminal::Terminal = term {
                    self.p = self.cp;
                } else {
                    self.p += 1;
                }
            },
            &CutInstruction::GetLevel => {
                let b0 = self.b0;
                let e  = self.e;

                self.and_stack[e].b0 = b0;
                self.p += 1;
            },
            &CutInstruction::NeckCut(ref term) => {
                let b = self.b;
                let b0 = self.b0;

                if b > b0 {
                    self.b = b0;
                    self.tidy_trail();
                }

                if let &Terminal::Terminal = term {
                    self.p = self.cp;
                } else {
                    self.p += 1;
                }
            }
        }
    }

    fn reset(&mut self) {
        self.h = 0;
        self.hb = 0;
        self.e = 0;
        self.b = 0;
        self.b0 = 0;
        self.s = 0;
        self.tr = 0;
        self.p = CodePtr::default();
        self.cp = CodePtr::default();
        self.num_of_args = 0;

        self.fail = false;
        self.trail.clear();
        self.heap.clear();
        self.mode = MachineMode::Write;
        self.and_stack.clear();
        self.or_stack.clear();
        self.registers = vec![Addr::HeapCell(0); 64];
        self.block = 0;
        self.ball = (0, Vec::new());
    }
}
