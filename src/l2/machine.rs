use l2::ast::*;
use l2::codegen::*;
use l2::heapview::*;
use l2::stack::*;

use std::collections::HashMap;
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
    cp: CodePtr,
    fail: bool,
    heap: Heap,
    mode: MachineMode,
    stack: Stack,
    registers: Registers
}

type CodeDir = HashMap<(Atom, usize), usize>;

pub struct Machine {
    ms: MachineState,
    code: Code,
    code_dir: CodeDir
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
        let p = self.code.len();
        let name  = fact.name().clone();
        let arity = fact.arity();

        self.code.append(&mut code);
        self.code_dir.insert((name, arity), p);
    }

    pub fn add_rule(&mut self, rule: &Rule, mut code: Code) {
        let p = self.code.len();
        let name  = rule.head.0.name().clone();
        let arity = rule.head.0.arity();

        self.code.append(&mut code);
        self.code_dir.insert((name, arity), p);
    }

    fn execute_instr(&mut self, instr: &Line) -> bool {
        let mut instr = instr;

        loop {
            match instr {
                &Line::Fact(ref fact) => {
                    for fact_instr in fact {
                        self.ms.execute_fact_instr(&fact_instr);
                    }
                    self.ms.p += 1;
                },
                &Line::Query(ref query) => {
                    for query_instr in query {
                        self.ms.execute_query_instr(&query_instr);
                    }
                    self.ms.p += 1;
                },
                &Line::Control(ref control_instr) =>
                    self.ms.execute_ctrl_instr(&self.code_dir, control_instr),
            }

            if self.failed() {
                return false;
            }

            match self.ms.p {
                CodePtr::DirEntry(p) if p < self.code.len() =>
                    instr = &self.code[p],
                _ => break
            }
        }

        true
    }

    fn heap_view(&self, var_dir: HashMap<&Var, HeapCellRef>) -> String {
        let mut result = String::new();        
        
        for (var, hcr) in var_dir {
            let mut arities = Vec::new();
            let viewer = HeapCellViewer::new(&self.ms.heap, hcr.heap_offset());

            if result != "" {
                result += "\n";
            }

            result += var.as_str();
            result += " = ";

            for view in viewer {
                match arities.pop() {
                    Some(n) => arities.push(n-1),
                    None => {}
                }

                if !(arities.is_empty() || result.ends_with("(")) {
                    result += ", ";
                }

                match view {
                    HeapCellView::Str(arity, ref name) => {
                        result += name.as_str();

                        if arity > 0 {
                            arities.push(arity);
                            result += "(";
                        }
                    },
                    HeapCellView::Var(cell_num) => {
                        result += "_";
                        result += cell_num.to_string().as_str();
                    }
                }

                while let Some(&0) = arities.last() {
                    result += ")";
                    arities.pop();
                }
            }
        }

        result
    }

    pub fn run_query(&mut self, code: Code, cg: &CodeGenerator) -> Option<String>
    {
        let mut succeeded = true;

        for instr in code.iter().take(1) {
            succeeded = self.execute_instr(&instr);
        }

        let mut heap_locs = HashMap::new();

        if succeeded {            
            for (var, vr) in cg.vars() {
                let hcr = self.ms.registers[vr.root_register()];
                heap_locs.insert(*var, hcr);
            }

            for instr in code.iter().skip(1) {
                succeeded = self.execute_instr(&instr);
                if !succeeded {
                    break;
                }
            }
        }
        
        if succeeded {
            Some(self.heap_view(heap_locs))
        } else {
            None
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
                       cp: CodePtr::TopLevel,
                       fail: false,
                       heap: Vec::with_capacity(256),
                       mode: MachineMode::Write,
                       stack: Stack::new(),
                       registers: vec![HeapCellRef::Ref(0); 32] }
    }

    fn register_mut(&mut self, r: RegType) -> &mut HeapCellRef {
        match r {
            RegType::Temp(r) => &mut self.registers[r],
            RegType::Perm(r) => &mut self.stack[r]
        }
    }

    fn lookup(&self, a: Addr) -> HeapCellRef {
        match a {
            Addr::HeapCell(r)  => self.heap[r].as_ref(r),
            Addr::RegNum(r)    => self.registers[r],
            Addr::StackCell(s) => self.stack[s]
        }
    }

    fn deref(&self, a: Addr) -> Addr {
        let mut a = a;

        loop {
            if let HeapCellRef::Ref(value) = self.lookup(a) {
                if let Addr::HeapCell(av) = a {
                    if value != av {
                        a = Addr::HeapCell(value);
                        continue;
                    }
                } else {
                    a = Addr::HeapCell(value);
                    continue;
                }
            }

            return a;
        };
    }

    fn is_unbound(hc: &HeapCellValue, index: usize) -> bool {
        match hc {
            &HeapCellValue::Ref(r) => r == index,
            _ => false
        }
    }

    fn bind(&mut self, a: Addr, val: usize) {
        let mut a = a;

        loop {
            match a {
                addr @ Addr::RegNum(_) | addr @ Addr::StackCell(_) => {
                    if let HeapCellRef::Ref(hc) = self.lookup(addr) {
                        a = Addr::HeapCell(hc);
                    } else if Self::is_unbound(&self.heap[val], val) {
                        self.heap[val] = HeapCellValue::from(self.lookup(addr));
                        break;
                    } else {
                        self.fail = true;
                        break;
                    }
                },
                Addr::HeapCell(hc) => {
                    if Self::is_unbound(&self.heap[hc], hc) {
                        self.heap[hc] = HeapCellValue::Ref(val);
                        break;
                    } else if Self::is_unbound(&self.heap[val], val) {
                        self.heap[val] = HeapCellValue::Ref(hc);
                        break;
                    } else {
                        self.fail = true;
                        break;
                    }
                }
            };
        }
    }

    fn unify(&mut self, a1: Addr, a2: Addr) {
        let mut pdl = vec![a1, a2];

        self.fail = false;

        while !(pdl.is_empty() || self.fail) {
            let d1 = self.deref(pdl.pop().unwrap());
            let d2 = self.deref(pdl.pop().unwrap());

            if d1 != d2 {
                match (self.lookup(d1), self.lookup(d2)) {
                    (HeapCellRef::Ref(hc), _) =>
                        self.bind(d2, hc),
                    (_, HeapCellRef::Ref(hc)) =>
                        self.bind(d1, hc),
                    (HeapCellRef::Str(a1), HeapCellRef::Str(a2)) => {
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
                };
            }
        }
    }

    fn execute_query_instr(&mut self, instr: &QueryInstruction) {
        match instr {
            &QueryInstruction::PutStructure(_, ref name, arity, reg) => {
                self.heap.push(HeapCellValue::Str(self.h + 1));
                self.heap.push(HeapCellValue::NamedStr(arity, name.clone()));

                *self.register_mut(reg) = HeapCellRef::Str(self.h + 1);

                self.h += 2;
            },
            &QueryInstruction::PutValue(norm, arg) =>
                self.registers[arg] = match norm {
                    RegType::Temp(reg) => self.registers[reg],
                    RegType::Perm(reg) => self.stack[reg]
                },
            &QueryInstruction::PutVariable(norm, arg) => {
                self.heap.push(HeapCellValue::Ref(self.h));

                *self.register_mut(norm) = HeapCellRef::Ref(self.h);
                self.registers[arg] = HeapCellRef::Ref(self.h);

                self.h += 1;
            },
            &QueryInstruction::SetVariable(reg) => {
                self.heap.push(HeapCellValue::Ref(self.h));
                *self.register_mut(reg) = HeapCellRef::Ref(self.h);

                self.h += 1;
            },
            &QueryInstruction::SetValue(reg) => {
                let heap_val = self.lookup(Addr::from(reg));
                self.heap.push(HeapCellValue::from(heap_val));

                self.h += 1;
            },
        }
    }

    fn execute_fact_instr(&mut self, instr: &FactInstruction) {
        match instr {
            &FactInstruction::GetStructure(_, ref name, arity, reg) => {
                let addr = self.deref(Addr::from(reg));

                match self.lookup(addr) {
                    HeapCellRef::Str(a) => {
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
                    HeapCellRef::Ref(_) => {
                        self.heap.push(HeapCellValue::Str(self.h + 1));
                        self.heap.push(HeapCellValue::NamedStr(arity, name.clone()));

                        let h = self.h;

                        self.bind(addr, h);

                        self.h += 2;
                        self.mode = MachineMode::Write;
                    }
                };
            },
            &FactInstruction::GetVariable(norm, arg) =>
                *self.register_mut(norm) = self.registers[arg],
            &FactInstruction::GetValue(norm, arg) =>
                self.unify(Addr::from(norm), Addr::RegNum(arg)),
            &FactInstruction::UnifyVariable(reg) => {
                match self.mode {
                    MachineMode::Read  =>
                        *self.register_mut(reg) = self.heap[self.s].as_ref(self.s),
                    MachineMode::Write => {
                        self.heap.push(HeapCellValue::Ref(self.h));
                        *self.register_mut(reg) = HeapCellRef::Ref(self.h);
                        self.h += 1;
                    }
                };

                self.s += 1;
            },
            &FactInstruction::UnifyValue(reg) => {
                let s = self.s;

                match self.mode {
                    MachineMode::Read  =>
                        self.unify(Addr::from(reg), Addr::HeapCell(s)),
                    MachineMode::Write => {
                        let heap_val = self.lookup(Addr::from(reg));
                        self.heap.push(HeapCellValue::from(heap_val));
                        self.h += 1;
                    }
                };

                self.s += 1;
            }
        }
    }

    fn execute_ctrl_instr(&mut self, code_dir: &CodeDir, instr: &ControlInstruction)
    {
        match instr {
            &ControlInstruction::Allocate(num_cells) => {
                self.stack.push(self.cp, num_cells);
                self.p += 1;
            },
            &ControlInstruction::Call(ref name, arity) => {
                let compiled_tl_index = code_dir.get(&(name.clone(), arity))
                                                .map(|index| *index);

                match compiled_tl_index {
                    Some(compiled_tl_index) => {
                        self.cp = self.p + 1;
                        self.p  = CodePtr::DirEntry(compiled_tl_index);
                    },
                    None => self.fail = true
                };
            },
            &ControlInstruction::Deallocate => {
                self.p = self.stack.get_cp();
                self.stack.pop();
            },
            &ControlInstruction::Proceed =>
                self.p = self.cp,
        };
    }

    fn reset(&mut self) {
        self.h = 0;
        self.s = 0;
        self.p = CodePtr::TopLevel;
        self.cp = CodePtr::TopLevel;

        self.fail = false;
        self.heap.clear();
        self.mode = MachineMode::Write;
        self.stack = Stack::new();
        self.registers = vec![HeapCellRef::Ref(0); 32];
    }
}
