use crate::parser::ast::*;

use crate::atom_table::*;
use crate::clause_types::*;
use crate::forms::*;
use crate::instructions::*;
use crate::iterators::*;
use crate::types::*;

pub(crate) trait CompilationTarget<'a> {
    type Iterator: Iterator<Item = TermRef<'a>>;

    fn iter(term: &'a Term) -> Self::Iterator;

    fn to_constant(lvl: Level, literal: Literal, r: RegType) -> Self;
    fn to_list(lvl: Level, r: RegType) -> Self;
    fn to_structure(ct: ClauseType, arity: usize, r: RegType) -> Self;

    fn to_void(num_subterms: usize) -> Self;
    fn is_void_instr(&self) -> bool;

    fn to_pstr(lvl: Level, string: Atom, r: RegType, has_tail: bool) -> Self;

    fn incr_void_instr(&mut self);

    fn constant_subterm(literal: Literal) -> Self;

    fn argument_to_variable(r: RegType, r: usize) -> Self;
    fn argument_to_value(r: RegType, val: usize) -> Self;

    fn move_to_register(r: RegType, val: usize) -> Self;

    fn subterm_to_variable(r: RegType) -> Self;
    fn subterm_to_value(r: RegType) -> Self;

    fn clause_arg_to_instr(r: RegType) -> Self;
}

impl<'a> CompilationTarget<'a> for FactInstruction {
    type Iterator = FactIterator<'a>;

    fn iter(term: &'a Term) -> Self::Iterator {
        breadth_first_iter(term, false) // do not iterate over the root clause if one exists.
    }

    fn to_constant(lvl: Level, constant: Literal, reg: RegType) -> Self {
        FactInstruction::GetConstant(lvl, HeapCellValue::from(constant), reg)
    }

    fn to_structure(ct: ClauseType, arity: usize, reg: RegType) -> Self {
        FactInstruction::GetStructure(ct, arity, reg)
    }

    fn to_list(lvl: Level, reg: RegType) -> Self {
        FactInstruction::GetList(lvl, reg)
    }

    fn to_void(num_subterms: usize) -> Self {
        FactInstruction::UnifyVoid(num_subterms)
    }

    fn is_void_instr(&self) -> bool {
        match self {
            &FactInstruction::UnifyVoid(_) => true,
            _ => false,
        }
    }

    fn to_pstr(lvl: Level, string: Atom, r: RegType, has_tail: bool) -> Self {
        FactInstruction::GetPartialString(lvl, string, r, has_tail)
    }

    fn incr_void_instr(&mut self) {
        match self {
            &mut FactInstruction::UnifyVoid(ref mut incr) => *incr += 1,
            _ => {}
        }
    }

    fn constant_subterm(constant: Literal) -> Self {
        FactInstruction::UnifyConstant(HeapCellValue::from(constant))
    }

    fn argument_to_variable(arg: RegType, val: usize) -> Self {
        FactInstruction::GetVariable(arg, val)
    }

    fn move_to_register(arg: RegType, val: usize) -> Self {
        FactInstruction::GetVariable(arg, val)
    }

    fn argument_to_value(arg: RegType, val: usize) -> Self {
        FactInstruction::GetValue(arg, val)
    }

    fn subterm_to_variable(val: RegType) -> Self {
        FactInstruction::UnifyVariable(val)
    }

    fn subterm_to_value(val: RegType) -> Self {
        FactInstruction::UnifyValue(val)
    }

    fn clause_arg_to_instr(val: RegType) -> Self {
        FactInstruction::UnifyVariable(val)
    }
}

impl<'a> CompilationTarget<'a> for QueryInstruction {
    type Iterator = QueryIterator<'a>;

    fn iter(term: &'a Term) -> Self::Iterator {
        post_order_iter(term)
    }

    fn to_structure(ct: ClauseType, arity: usize, r: RegType) -> Self {
        QueryInstruction::PutStructure(ct, arity, r)
    }

    fn to_constant(lvl: Level, constant: Literal, reg: RegType) -> Self {
        QueryInstruction::PutConstant(lvl, HeapCellValue::from(constant), reg)
    }

    fn to_list(lvl: Level, reg: RegType) -> Self {
        QueryInstruction::PutList(lvl, reg)
    }

    fn to_pstr(lvl: Level, string: Atom, r: RegType, has_tail: bool) -> Self {
        QueryInstruction::PutPartialString(lvl, string, r, has_tail)
    }

    fn to_void(subterms: usize) -> Self {
        QueryInstruction::SetVoid(subterms)
    }

    fn is_void_instr(&self) -> bool {
        match self {
            &QueryInstruction::SetVoid(_) => true,
            _ => false,
        }
    }

    fn incr_void_instr(&mut self) {
        match self {
            &mut QueryInstruction::SetVoid(ref mut incr) => *incr += 1,
            _ => {}
        }
    }

    fn constant_subterm(constant: Literal) -> Self {
        QueryInstruction::SetConstant(HeapCellValue::from(constant))
    }

    fn argument_to_variable(arg: RegType, val: usize) -> Self {
        QueryInstruction::PutVariable(arg, val)
    }

    fn move_to_register(arg: RegType, val: usize) -> Self {
        QueryInstruction::GetVariable(arg, val)
    }

    fn argument_to_value(arg: RegType, val: usize) -> Self {
        QueryInstruction::PutValue(arg, val)
    }

    fn subterm_to_variable(val: RegType) -> Self {
        QueryInstruction::SetVariable(val)
    }

    fn subterm_to_value(val: RegType) -> Self {
        QueryInstruction::SetValue(val)
    }

    fn clause_arg_to_instr(val: RegType) -> Self {
        QueryInstruction::SetValue(val)
    }
}
