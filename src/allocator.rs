use crate::parser::ast::*;

use crate::forms::*;
use crate::instructions::*;
use crate::targets::*;

use std::cell::Cell;

pub(crate) trait Allocator {
    fn new() -> Self;

    fn mark_anon_var<'a, Target: CompilationTarget<'a>>(
        &mut self,
        lvl: Level,
        context: GenContext,
        code: &mut CodeDeque,
    );

    fn mark_non_var<'a, Target: CompilationTarget<'a>>(
        &mut self,
        lvl: Level,
        context: GenContext,
        cell: &'a Cell<RegType>,
        code: &mut CodeDeque,
    );

    #[allow(clippy::too_many_arguments)]
    fn mark_reserved_var<'a, Target: CompilationTarget<'a>>(
        &mut self,
        var_num: usize,
        lvl: Level,
        cell: &Cell<VarReg>,
        term_loc: GenContext,
        code: &mut CodeDeque,
        r: RegType,
        is_new_var: bool,
    );

    fn mark_cut_var(&mut self, var_num: usize, chunk_num: usize) -> RegType;

    fn mark_var<'a, Target: CompilationTarget<'a>>(
        &mut self,
        var_num: usize,
        lvl: Level,
        cell: &Cell<VarReg>,
        context: GenContext,
        code: &mut CodeDeque,
    );

    fn reset(&mut self);
    fn reset_arg(&mut self, arg_num: usize);
    fn reset_at_head(&mut self, args: &[Term]);
    fn reset_contents(&mut self);

    fn advance_arg(&mut self);
    fn max_reg_allocated(&self) -> usize;
}
