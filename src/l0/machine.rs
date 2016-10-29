use l0::ast::{Addr, Atom, MachineInstruction, Program, Term, TopLevel, Var};

use std::fmt;
use std::vec::{Vec};

#[derive(Clone)]
enum HeapCell {
    NamedStr(usize, Atom),
    Ref(usize), // these offsets are always in reference to cells on the Heap!
    Str(usize),
}

#[derive(Clone, Copy)]
enum MachineMode {
    Read,
    Write
}

type Heap = Vec<HeapCell>;

type Registers = Vec<HeapCell>;

pub struct MachineState {
    h : usize,
    s : usize,
    pub fail : bool,
    heap : Heap,
    mode : MachineMode,
    pub program : Option<Program>,
    registers : Registers
}

impl MachineState {
    pub fn new() -> MachineState {
        MachineState { h : 0,
                       s : 0,
                       fail : false,
                       heap : Vec::with_capacity(256),
                       mode : MachineMode::Write,
                       program : None,
                       registers : vec![HeapCell::Ref(0); 33] }
    }
    
    fn lookup(&self, a: Addr) -> &HeapCell {
        match a {
            Addr::HeapCell(hc) => &self.heap[hc],
            Addr::RegNum(reg)  => &self.registers[reg]
        }
    }

    fn deref(&self, a: Addr) -> Addr {
        let mut a = a;

        loop {
            if let &HeapCell::Ref(value) = self.lookup(a) {
                if value != a.heap_offset() {
                    a = Addr::HeapCell(value);
                    continue;
                } else {
                    return a;
                }
            }

            return a;
        };
    }

    fn bind(&mut self, a: Addr, val: Addr) {
        match a {
            Addr::RegNum(reg)  => self.registers[reg] = HeapCell::Ref(val.heap_offset()),
            Addr::HeapCell(hc) => self.heap[hc] = HeapCell::Ref(val.heap_offset()),
        };
    }

    fn unify(&mut self, a1: Addr, a2: Addr) {
        let mut pdl : Vec<Addr> = vec![a1, a2];

        self.fail = false;

        while !(pdl.is_empty() || self.fail) {
            let d1 = self.deref(pdl.pop().unwrap());
            let d2 = self.deref(pdl.pop().unwrap());

            if d1 != d2 {
                match (self.lookup(d1), self.lookup(d2)) {
                    (&HeapCell::Ref(_), _) | (_, &HeapCell::Ref(_)) =>
                        self.bind(d1, d2),
                    (&HeapCell::Str(a1), &HeapCell::Str(a2)) => {
                        let r1 = &self.heap[a1];
                        let r2 = &self.heap[a2];

                        if let &HeapCell::NamedStr(n1, ref f1) = r1 {
                            if let &HeapCell::NamedStr(n2, ref f2) = r2 {
                                if n1 == n2 && *f1 == *f2 {
                                    for i in 1 .. n1 {
                                        pdl.push(Addr::HeapCell(a1 + i));
                                        pdl.push(Addr::HeapCell(a2 + i));
                                    }

                                    continue;
                                }
                            }
                        }

                        self.fail = true;
                    },
                    _ => self.fail = true,
                };
            }
        }
    }    
    
    pub fn execute(&mut self, instr: MachineInstruction) {
        match instr {
            MachineInstruction::GetStructure(name, arity, reg) => {
                let addr = self.deref(Addr::RegNum(reg));

                match self.lookup(addr) {
                    &HeapCell::Str(a) => {
                        let result = &self.heap[a];

                        if let &HeapCell::NamedStr(named_arity, ref named_str) = result {
                            if arity == named_arity && name == *named_str {
                                self.s = a + 1;
                                self.mode = MachineMode::Read;
                            } else {
                                self.fail = true;
                            }
                        }
                    },
                    &HeapCell::Ref(reg) => {
                        self.heap.push(HeapCell::Str(self.h + 1));
                        self.heap.push(HeapCell::NamedStr(arity, name));

                        let h = self.h;

                        self.bind(Addr::RegNum(reg), Addr::HeapCell(h));

                        self.h += 2;
                        self.mode = MachineMode::Write;
                    },
                    _ => {
                        self.fail = true;
                    }
                };
            },
            MachineInstruction::PutStructure(name, arity, reg) => {
                self.heap.push(HeapCell::Str(self.h + 1));
                self.heap.push(HeapCell::NamedStr(arity, name));

                self.registers[reg] = self.heap[self.h].clone();

                self.h += 2;
            },
            MachineInstruction::SetVariable(reg) => {
                self.heap.push(HeapCell::Ref(self.h));
                self.registers[reg] = self.heap[self.h].clone();

                self.h += 1;
            },
            MachineInstruction::SetValue(reg) => {
                self.heap.push(self.registers[reg].clone());
                self.h += 1;
            },
            MachineInstruction::UnifyVariable(reg) => {
                match self.mode {
                    MachineMode::Read  => self.registers[reg] = self.heap[self.s].clone(),
                    MachineMode::Write => {
                        self.heap.push(HeapCell::Ref(self.h));
                        self.registers[reg] = self.heap[self.h].clone();
                        self.h += 1;
                    }
                };                    
            },
            MachineInstruction::UnifyValue(reg) => {
                let s = self.s;

                match self.mode {
                    MachineMode::Read  => self.unify(Addr::RegNum(reg), Addr::HeapCell(s)),
                    MachineMode::Write => {
                        self.heap.push(self.registers[reg].clone());
                        self.h += 1;
                    }
                };
                
                self.s += 1;
            }
        }
    }
    
    pub fn reset_heap(&mut self) {
        let program = self.program.take();

        *self = MachineState::new();
        self.program = program;
    }
    
    pub fn dump_registers_and_heap(&self) {
        let mut c = 0;

        let printer = |contents, c| {
            match contents {
                &HeapCell::NamedStr(ref arity, ref atom) => {
                    println!("{} = NAME({}, {})", c, arity, atom);
                },
                &HeapCell::Ref(hc) => {
                    println!("{} = REF({})", c, hc);
                },
                &HeapCell::Str(hc) => {
                    println!("{} = STR({})", c, hc);
                }
            };
        };
        
        for contents in &self.registers {
            print!("X");
            printer(contents, c);
            c += 1;
        }

        println!("");
        
        c = 0;

        for contents in &self.heap {
            printer(contents, c);
            c += 1;
        }
    }
}
