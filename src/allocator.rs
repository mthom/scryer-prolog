use crate::parser::ast::*;

use crate::forms::*;
use crate::instructions::*;
use crate::targets::*;

pub(crate) trait Allocator {
    fn new() -> Self;

    fn mark_anon_var<'a, Target: CompilationTarget<'a>>(
        &mut self,
        lvl: Level,
        context: GenContext,
        code: &mut CodeDeque,
    ) -> RegType;

    fn mark_non_var<'a, Target: CompilationTarget<'a>>(
        &mut self,
        lvl: Level,
        heap_loc: usize,
        context: GenContext,
        code: &mut CodeDeque,
    ) -> RegType;

    #[allow(clippy::too_many_arguments)]
    fn mark_reserved_var<'a, Target: CompilationTarget<'a>>(
        &mut self,
        var_num: usize,
        lvl: Level,
        context: GenContext,
        code: &mut CodeDeque,
        r: RegType,
        is_new_var: bool,
    ) -> RegType;

    fn mark_cut_var(&mut self, var_num: usize, chunk_num: usize) -> RegType;

    fn mark_var<'a, Target: CompilationTarget<'a>>(
        &mut self,
        var_num: usize,
        lvl: Level,
        context: GenContext,
        code: &mut CodeDeque,
    ) -> RegType;

    fn reset(&mut self);
    fn reset_arg(&mut self, arg_num: usize);
    fn reset_at_head(&mut self, term: &mut FocusedHeap, head_loc: usize);
    fn reset_contents(&mut self);

    fn advance_arg(&mut self);
    fn max_reg_allocated(&self) -> usize;
}
