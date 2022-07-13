use crate::parser::ast::*;

use crate::atom_table::*;
use crate::forms::*;
use crate::instructions::*;
use crate::iterators::*;
use crate::types::*;

pub(crate) struct FactInstruction;
pub(crate) struct QueryInstruction;

pub(crate) trait CompilationTarget<'a> {
    type Iterator: Iterator<Item = TermRef<'a>>;

    fn iter(term: &'a Term) -> Self::Iterator;

    fn to_constant(lvl: Level, literal: Literal, r: RegType) -> Instruction;
    fn to_list(lvl: Level, r: RegType) -> Instruction;
    fn to_structure(name: Atom, arity: usize, r: RegType) -> Instruction;

    fn to_void(num_subterms: usize) -> Instruction;
    fn is_void_instr(instr: &Instruction) -> bool;

    fn to_pstr(lvl: Level, string: Atom, r: RegType, has_tail: bool) -> Instruction;

    fn incr_void_instr(instr: &mut Instruction);

    fn constant_subterm(literal: Literal) -> Instruction;

    fn argument_to_variable(r: RegType, r: usize) -> Instruction;
    fn argument_to_value(r: RegType, val: usize) -> Instruction;

    fn move_to_register(r: RegType, val: usize) -> Instruction;

    fn subterm_to_variable(r: RegType) -> Instruction;
    fn subterm_to_value(r: RegType) -> Instruction;

    fn clause_arg_to_instr(r: RegType) -> Instruction;

    fn trim_structure_by_last_arg(instr: &mut Instruction, last_arg: &Term);
}

impl<'a> CompilationTarget<'a> for FactInstruction {
    type Iterator = FactIterator<'a>;

    fn iter(term: &'a Term) -> Self::Iterator {
        breadth_first_iter(term, false) // do not iterate over the root clause if one exists.
    }

    fn to_constant(lvl: Level, constant: Literal, reg: RegType) -> Instruction {
        Instruction::GetConstant(lvl, HeapCellValue::from(constant), reg)
    }

    fn to_structure(name: Atom, arity: usize, reg: RegType) -> Instruction {
        Instruction::GetStructure(name, arity, reg)
    }

    fn to_list(lvl: Level, reg: RegType) -> Instruction {
        Instruction::GetList(lvl, reg)
    }

    fn to_void(num_subterms: usize) -> Instruction {
        Instruction::UnifyVoid(num_subterms)
    }

    fn is_void_instr(instr: &Instruction) -> bool {
        match instr {
            &Instruction::UnifyVoid(_) => true,
            _ => false,
        }
    }

    fn to_pstr(lvl: Level, string: Atom, r: RegType, has_tail: bool) -> Instruction {
        Instruction::GetPartialString(lvl, string, r, has_tail)
    }

    fn incr_void_instr(instr: &mut Instruction) {
        match instr {
            &mut Instruction::UnifyVoid(ref mut incr) => *incr += 1,
            _ => {}
        }
    }

    fn constant_subterm(constant: Literal) -> Instruction {
        Instruction::UnifyConstant(HeapCellValue::from(constant))
    }

    fn argument_to_variable(arg: RegType, val: usize) -> Instruction {
        Instruction::GetVariable(arg, val)
    }

    fn move_to_register(arg: RegType, val: usize) -> Instruction {
        Instruction::GetVariable(arg, val)
    }

    fn argument_to_value(arg: RegType, val: usize) -> Instruction {
        Instruction::GetValue(arg, val)
    }

    fn subterm_to_variable(val: RegType) -> Instruction {
        Instruction::UnifyVariable(val)
    }

    fn subterm_to_value(val: RegType) -> Instruction {
        Instruction::UnifyValue(val)
    }

    fn clause_arg_to_instr(val: RegType) -> Instruction {
        Instruction::UnifyVariable(val)
    }

    fn trim_structure_by_last_arg(_instr: &mut Instruction, _last_arg: &Term) {
        // a no-op for facts.
    }
}

impl<'a> CompilationTarget<'a> for QueryInstruction {
    type Iterator = QueryIterator<'a>;

    fn iter(term: &'a Term) -> Self::Iterator {
        post_order_iter(term)
    }

    fn to_structure(name: Atom, arity: usize, r: RegType) -> Instruction {
        Instruction::PutStructure(name, arity, r)
    }

    fn to_constant(lvl: Level, constant: Literal, reg: RegType) -> Instruction {
        Instruction::PutConstant(lvl, HeapCellValue::from(constant), reg)
    }

    fn to_list(lvl: Level, reg: RegType) -> Instruction {
        Instruction::PutList(lvl, reg)
    }

    fn to_pstr(lvl: Level, string: Atom, r: RegType, has_tail: bool) -> Instruction {
        Instruction::PutPartialString(lvl, string, r, has_tail)
    }

    fn to_void(subterms: usize) -> Instruction {
        Instruction::SetVoid(subterms)
    }

    fn is_void_instr(instr: &Instruction) -> bool {
        match instr {
            &Instruction::SetVoid(_) => true,
            _ => false,
        }
    }

    fn incr_void_instr(instr: &mut Instruction) {
        match instr {
            &mut Instruction::SetVoid(ref mut incr) => *incr += 1,
            _ => {}
        }
    }

    fn constant_subterm(constant: Literal) -> Instruction {
        Instruction::SetConstant(HeapCellValue::from(constant))
    }

    fn argument_to_variable(arg: RegType, val: usize) -> Instruction {
        Instruction::PutVariable(arg, val)
    }

    fn move_to_register(arg: RegType, val: usize) -> Instruction {
        Instruction::GetVariable(arg, val)
    }

    fn argument_to_value(arg: RegType, val: usize) -> Instruction {
        Instruction::PutValue(arg, val)
    }

    fn subterm_to_variable(val: RegType) -> Instruction {
        Instruction::SetVariable(val)
    }

    fn subterm_to_value(val: RegType) -> Instruction {
        Instruction::SetValue(val)
    }

    fn clause_arg_to_instr(val: RegType) -> Instruction {
        Instruction::SetValue(val)
    }

    // if the final argument of the structure is a Literal::Index,
    // decrement the arity of the PutStructure instruction by 1.
    fn trim_structure_by_last_arg(instr: &mut Instruction, last_arg: &Term) {
        if let Instruction::PutStructure(_, ref mut arity, _) = instr {
            if let Term::Literal(_, Literal::CodeIndex(_)) = last_arg {
                // it is acceptable if arity == 0 is the result of
                // this decrement. call/N will have to read the index
                // constant for '$call_inline' to succeed. to find it,
                // it must know the heap location of the index.
                // self.store must stop before reading the atom into a
                // register.

                *arity -= 1;
            }
        }
    }
}
