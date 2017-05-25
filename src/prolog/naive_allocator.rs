use prolog::allocator::*;
use prolog::ast::*;
use prolog::fixtures::*;
use prolog::targets::*;

use std::cell::Cell;
use std::cmp::max;
use std::collections::HashMap;

pub struct NaiveAllocator<'a> {    
    bindings: AllocVarDict<'a>,
    arg_c:    usize,
    temp_c:   usize,
}
    
impl<'a> Allocator<'a> for NaiveAllocator<'a>
{
    fn new() -> Self {
        NaiveAllocator {
            arg_c:    1,
            temp_c:   1,
            bindings: HashMap::new(),
        }
    }
    
    fn mark_anon_var<Target>(&mut self, lvl: Level, target: &mut Vec<Target>)
        where Target: CompilationTarget<'a>
    {
        let r = {
            let temp = self.temp_c;
            self.temp_c += 1;
            RegType::Temp(temp)
        };

        match lvl {
            Level::Deep => target.push(Target::subterm_to_variable(r)),
            Level::Shallow => {
                let k = self.arg_c;
                self.arg_c += 1;

                target.push(Target::argument_to_variable(r, k));
            }
        }
    }

    fn mark_non_var<Target>(&mut self,
                            lvl: Level,
                            _: GenContext,
                            cell: &Cell<RegType>,
                            _: &mut Vec<Target>)
        where Target: CompilationTarget<'a>
    {
        let r = cell.get();

        if r.reg_num() == 0 {
            let r = match lvl {                
                Level::Shallow => {
                    let k = self.arg_c;
                    self.arg_c += 1;
                    
                    RegType::Temp(k)
                },
                _ => {
                    let temp = self.temp_c;
                    self.temp_c += 1;
                    
                    RegType::Temp(temp)
                }
            };

            cell.set(r);
        }
    }    

    fn mark_var<Target>(&mut self,
                        var: &'a Var,
                        lvl: Level,
                        cell: &'a Cell<VarReg>,
                        _: GenContext,
                        target: &mut Vec<Target>)
        where Target: CompilationTarget<'a>
    {
        let (r, is_new_var) = match self.get(var) {
            RegType::Temp(0) => {
                let o = self.temp_c;
                self.temp_c += 1;
                
                (RegType::Temp(o), true)
            },
            RegType::Perm(0) => {
                let pr = cell.get().norm();
                self.record_register(var, pr);
                
                (pr, true)
            },
            r => (r, false)
        };
        
        match lvl {            
            Level::Shallow => {
                let k = self.arg_c;                
                self.arg_c += 1;                               

                cell.set(VarReg::ArgAndNorm(r, k));
                
                if is_new_var {
                    target.push(Target::argument_to_variable(r, k));
                } else {
                    target.push(Target::argument_to_value(r, k));
                }                
            },
            Level::Deep => {
                cell.set(VarReg::Norm(r));

                if is_new_var {
                    target.push(Target::subterm_to_variable(r));
                } else {
                    target.push(Target::subterm_to_value(r));
                }
            }
        };

        if !r.is_perm() {
            self.record_register(var, r);
        }
    }
    
    fn reset(&mut self) {
        self.bindings.clear();
    }
    
    fn advance(&mut self, term_loc: GenContext, term: QueryTermRef<'a>) {
        if let GenContext::Head = term_loc {
            self.arg_c  = 1;
            self.temp_c = max(term.arity() + 1, self.temp_c);
        } else {
            self.arg_c  = 1;
            self.temp_c = term.arity() + 1;
        }
    }

    fn advance_arg(&mut self) {
        self.arg_c += 1;
    }

    fn bindings(&self) -> &AllocVarDict<'a> {
        &self.bindings
    }
    
    fn bindings_mut(&mut self) -> &mut AllocVarDict<'a> {
        &mut self.bindings
    }
    
    fn take_bindings(self) -> AllocVarDict<'a> {
        self.bindings
    }
}
