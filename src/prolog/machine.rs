use prolog::ast::*;
use prolog::codegen::*;
use prolog::heapview::*;
use prolog::and_stack::*;
use prolog::or_stack::*;

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
    hb: usize
}

type CodeDir = HashMap<(Atom, usize), usize>;

pub struct Machine {
    ms: MachineState,
    code: Code,
    code_dir: CodeDir
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

impl Machine {
    pub fn new() -> Self {
        Machine {
            ms: MachineState::new(),
            code: Vec::new(),
            code_dir: HashMap::new()
        }
    }

    pub fn failed(&self) -> bool {
        self.ms.fail
    }

    pub fn add_fact(&mut self, fact: &Term, mut code: Code) {
        if fact.name().is_some() {
            let p = self.code.len();
            let name  = fact.name().unwrap().clone();
            let arity = fact.arity();

            self.code.append(&mut code);
            self.code_dir.insert((name, arity), p);
        }
    }

    pub fn add_rule(&mut self, rule: &Rule, mut code: Code) {
        if rule.head.0.name().is_some() {
            let p = self.code.len();
            let name  = rule.head.0.name().unwrap().clone();
            let arity = rule.head.0.arity();

            self.code.append(&mut code);
            self.code_dir.insert((name, arity), p);
        }
    }

    pub fn add_predicate(&mut self, pred: &Vec<PredicateClause>, mut code: Code)
    {
        let p = self.code.len();
        let name  = pred.first().unwrap().name().clone();
        let arity = pred.first().unwrap().arity();

        self.code.append(&mut code);
        self.code_dir.insert((name, arity), p);
    }

    fn execute_instr<'a>(&mut self, instr_src: LineOrCodeOffset<'a>) -> bool
    {
        let mut instr = match instr_src {
            LineOrCodeOffset::Instruction(instr) => instr,
            LineOrCodeOffset::Offset(p) => &self.code[p]
        };

        loop {
            match instr {
                &Line::Choice(ref choice_instr) =>
                    self.ms.execute_choice_instr(choice_instr),
                &Line::Fact(ref fact) => {
                    for fact_instr in fact {
                        if self.failed() {
                            break;
                        }

                        self.ms.execute_fact_instr(&fact_instr);
                    }
                    self.ms.p += 1;
                },
                &Line::Query(ref query) => {
                    for query_instr in query {
                        if self.failed() {
                            break;
                        }

                        self.ms.execute_query_instr(&query_instr);
                    }
                    self.ms.p += 1;
                },
                &Line::Control(ref control_instr) =>
                    self.ms.execute_ctrl_instr(&self.code_dir, control_instr),
            }

            if self.failed() {
                let p = self.ms
                            .or_stack
                            .top()
                            .map(|fr| fr.bp)
                            .unwrap_or_default();

                if let CodePtr::TopLevel = p {
                    return false;
                } else {
                    self.ms.fail = false;
                    self.ms.p = p;
                }
            }

            match self.ms.p {
                CodePtr::DirEntry(p) if p < self.code.len() =>
                    instr = &self.code[p],
                _ => break
            }
        }

        true
    }

    pub fn heap_view(&self, var_dir: &HeapVarDict) -> String {
        let mut result = String::new();

        for (var, addr) in var_dir {
            let mut viewer = HeapCellViewer::new(&self.ms.heap,
                                                 &self.ms.and_stack,
                                                 addr);

            if result != "" {
                result += "\n\r";
            }

            result += var.as_str();
            result += " = ";

            while let Some(view) = viewer.next() {
                match view {
                    CellView::Con(&Constant::EmptyList) =>
                        result += "[]",
                    CellView::Con(&Constant::Atom(ref atom)) =>
                        result += atom.as_str(),
                    CellView::HeapVar(cell_num) => {
                        result += "_";
                        result += cell_num.to_string().as_str();
                    },
                    CellView::StackVar(fr, sc) => {
                        result += "_";
                        result += fr.to_string().as_str();
                        result += "_";
                        result += sc.to_string().as_str();
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
        }

        result
    }

    pub fn run_query(&mut self, code: Code, cg: &CodeGenerator) -> EvalResult
    {
        let mut succeeded = true;
        let mut heap_locs = HashMap::new();

        for instr in code.iter().take(1) {
            succeeded = self.execute_instr(LineOrCodeOffset::from(instr));
        }

        if succeeded {
            for (var, vr) in cg.vars() {
                let addr = self.ms.registers[vr.root_register()].clone();
                heap_locs.insert((*var).clone(), addr);
            }

            for instr in code.iter().skip(1) {
                succeeded = self.execute_instr(LineOrCodeOffset::from(instr));
                if !succeeded {
                    break;
                }
            }
        }

        if succeeded {
            EvalResult::InitialQuerySuccess(heap_locs)
        } else {
            EvalResult::QueryFailure
        }
    }

    pub fn or_stack_is_empty(&self) -> bool {
        self.ms.or_stack.is_empty()
    }

    pub fn continue_query(&mut self) -> EvalResult
    {
        if !self.or_stack_is_empty() {
            let b = self.ms.b;
            self.ms.p = self.ms.or_stack[b].bp;

            let succeeded = if let CodePtr::DirEntry(p) = self.ms.p {
                self.execute_instr(LineOrCodeOffset::Offset(p))
            } else {
                false
            };

            if succeeded {
                EvalResult::SubsequentQuerySuccess
            } else {
                EvalResult::QueryFailure
            }
        } else {
            EvalResult::QueryFailure
        }
    }

    pub fn reset(&mut self) {
        self.ms.reset();
    }
}

impl MachineState {
    fn new() -> MachineState {
        MachineState { h: 0,
                       s: 0,
                       p: CodePtr::TopLevel,
                       b: 0,
                       e: 0,
                       num_of_args: 0,
                       cp: CodePtr::TopLevel,
                       fail: false,
                       heap: Vec::with_capacity(256),
                       mode: MachineMode::Write,
                       and_stack: AndStack::new(),
                       or_stack: OrStack::new(),
                       registers: vec![Addr::HeapCell(0); 64],
                       trail: Vec::new(),
                       tr: 0,
                       hb: 0
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
                    self.or_stack[self.b].global_index
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

    fn execute_fact_instr(&mut self, instr: &FactInstruction) {
        match instr {
            &FactInstruction::GetConstant(_, ref constant, reg) => {
                let addr = self.deref(self[reg].clone());

                match self.store(addr) {
                    Addr::HeapCell(hc) => {
                        self.heap[hc] = HeapCellValue::Con(constant.clone());
                        self.trail(Ref::HeapCell(hc));
                    },
                    Addr::StackCell(fr, sc) => {
                        self.and_stack[fr][sc] = Addr::Con(constant.clone());
                        self.trail(Ref::StackCell(fr, sc));
                    },
                    Addr::Con(c) => {
                        if c != *constant {
                            self.fail = true;
                        }
                    },
                    _ => self.fail = true
                };
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
                        let addr = self.deref(Addr::HeapCell(self.s));

                        match self.store(addr) {
                            Addr::HeapCell(hc) =>
                                self.heap[hc] = HeapCellValue::Con(c.clone()),
                            Addr::StackCell(fr, sc) =>
                                self.and_stack[fr][sc] = Addr::Con(c.clone()),
                            Addr::Con(c1) => {
                                if c1 != *c {
                                    self.fail = true;
                                }
                            },
                            _ => self.fail = true
                        };
                    },
                    MachineMode::Write => {
                        self.heap.push(HeapCellValue::Con(c.clone()));
                        self.h += 1;
                    }
                };
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
            }
        };
    }

    fn execute_query_instr(&mut self, instr: &QueryInstruction) {
        match instr {
            &QueryInstruction::PutConstant(_, ref constant, reg) =>
                self[reg] = Addr::Con(constant.clone()),
            &QueryInstruction::PutList(_, reg) =>
                self[reg] = Addr::Lis(self.h),
            &QueryInstruction::PutStructure(_, ref name, arity, reg) => {
                self.heap.push(HeapCellValue::NamedStr(arity, name.clone()));
                self[reg] = Addr::Str(self.h);
                self.h += 1;
            },
            &QueryInstruction::PutValue(norm, arg) =>
                self.registers[arg] = self[norm].clone(),
            &QueryInstruction::PutVariable(norm, arg) => {
                let h = self.h;
                self.heap.push(HeapCellValue::Ref(Ref::HeapCell(h)));

                self[norm] = Addr::HeapCell(h);
                self.registers[arg] = Addr::HeapCell(h);

                self.h += 1;
            },
            &QueryInstruction::SetConstant(ref constant) => {
                self.heap.push(HeapCellValue::Con(constant.clone()));
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
        }
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
            &ControlInstruction::Call(ref name, arity) => {
                let compiled_tl_index = code_dir.get(&(name.clone(), arity))
                                                .map(|index| *index);

                match compiled_tl_index {
                    Some(compiled_tl_index) => {
                        self.cp = self.p + 1;
                        self.num_of_args = arity;
                        self.p  = CodePtr::DirEntry(compiled_tl_index);
                    },
                    None => self.fail = true
                };
            },
            &ControlInstruction::Deallocate => {
                let e = self.e;

                let num_frame_e = self.and_stack.top().unwrap().global_index;
                let num_frame_b = self.or_stack
                                      .top()
                                      .map(|fr| fr.global_index)
                                      .unwrap_or(0);

                self.p = self.and_stack[e].cp;
                self.e = self.and_stack[e].e;

                if num_frame_e > num_frame_b {
                    let top_e = self.and_stack.top().unwrap().e;
                    self.and_stack.drop_frames(top_e - self.e + 1);
                }
            },
            &ControlInstruction::Proceed =>
                self.p = self.cp,
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
                                   self.num_of_args);

                self.b = self.or_stack.len() - 1;
                let b = self.b;

                for i in 1 .. n + 1 {
                    self.or_stack[b][i] = self.registers[i].clone();
                }

                self.hb = self.h;
                self.p += 1;
            },
            &ChoiceInstruction::RetryMeElse(offset) => {
                let b = self.b;
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
                let b = self.b;
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

    fn reset(&mut self) {
        self.h = 0;
        self.hb = 0;
        self.e = 0;
        self.b = 0;
        self.s = 0;
        self.tr = 0;
        self.p = CodePtr::TopLevel;
        self.cp = CodePtr::TopLevel;
        self.num_of_args = 0;

        self.fail = false;
        self.trail.clear();
        self.heap.clear();
        self.mode = MachineMode::Write;
        self.and_stack.clear();
        self.or_stack.clear();
        self.registers = vec![Addr::HeapCell(0); 64];
    }
}
