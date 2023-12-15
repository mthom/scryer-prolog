use crate::atom_table::*;
use crate::codegen::*;
use crate::forms::*;
use crate::indexing::{merge_clause_index, remove_index};
use crate::instructions::*;
use crate::machine::load_state::*;
use crate::machine::loader::*;
use crate::machine::machine_errors::*;
use crate::machine::preprocessor::*;
use crate::machine::term_stream::*;
use crate::machine::*;
use crate::parser::ast::*;

use std::cell::Cell;
use std::collections::VecDeque;
use std::mem;
use std::ops::Range;

struct StandaloneCompileResult {
    clause_code: Code,
    standalone_skeleton: PredicateSkeleton,
}

pub(super) fn bootstrapping_compile(
    stream: Stream,
    wam: &mut Machine,
    listing_src: ListingSource,
) -> Result<(), SessionError> {
    let (wam_prelude, machine_st) = wam.prelude_view_and_machine_st();

    let term_stream = BootstrappingTermStream::from_char_reader(stream, machine_st, listing_src);

    let payload =
        BootstrappingLoadState(LoadStatePayload::new(wam_prelude.code.len(), term_stream));

    let loader: Loader<'_, BootstrappingLoadState> = Loader {
        payload,
        wam_prelude,
    };

    loader.load()?;
    Ok(())
}

fn lower_bound_of_target_clause(skeleton: &mut PredicateSkeleton, target_pos: usize) -> usize {
    if target_pos == 0 {
        return 0;
    }

    let index = target_pos - 1;
    let arg_num = skeleton.clauses[index].opt_arg_index_key.arg_num();

    if arg_num == 0 {
        return index;
    }

    skeleton
        .clauses[target_pos]
        .opt_arg_index_key
        .switch_on_term_loc()
        .map(|index_loc| {
            let search_result = skeleton.clauses.make_contiguous()
                [0 .. skeleton.core.clause_assert_margin]
                .partition_point(|clause_index_info| {
                    clause_index_info.clause_start > index_loc
                });

            if search_result < skeleton.core.clause_assert_margin {
                search_result
            } else {
                skeleton.clauses.make_contiguous()[skeleton.core.clause_assert_margin ..]
                    .partition_point(|clause_index_info| {
                        clause_index_info.clause_start < index_loc
                    }) + skeleton.core.clause_assert_margin
            }
        }).unwrap_or(index)
}

fn derelictize_try_me_else(
    code: &mut Code,
    index: usize,
    retraction_info: &mut RetractionInfo,
) -> Option<usize> {
    match &mut code[index] {
        Instruction::DynamicElse(_, _, NextOrFail::Next(0)) => None,
        Instruction::DynamicElse(_, _, NextOrFail::Next(ref mut o)) => {
            retraction_info.push_record(RetractionRecord::ReplacedDynamicElseOffset(index, *o));
            Some(mem::replace(o, 0))
        }
        Instruction::DynamicInternalElse(_, _, NextOrFail::Next(0)) => None,
        Instruction::DynamicInternalElse(_, _, NextOrFail::Next(ref mut o)) => {
            retraction_info.push_record(RetractionRecord::ReplacedDynamicElseOffset(index, *o));
            Some(mem::replace(o, 0))
        }
        Instruction::DynamicElse(_, _, NextOrFail::Fail(_))
        | Instruction::DynamicInternalElse(_, _, NextOrFail::Fail(_)) => None,
        Instruction::TryMeElse(0) => None,
        Instruction::TryMeElse(ref mut o) => {
            retraction_info.push_record(RetractionRecord::ModifiedTryMeElse(index, *o));
            Some(mem::replace(o, 0))
        }
        _ => {
            unreachable!()
        }
    }
}

fn merge_indices(
    code: &mut Code,
    target_index_loc: usize,
    index_range: Range<usize>,
    skeleton: &mut [ClauseIndexInfo],
    retracted_dynamic_clauses: &Option<Vec<ClauseIndexInfo>>,
    retraction_info: &mut RetractionInfo,
) {
    for clause_index in index_range {
        if let Some(index_loc) = skeleton[clause_index]
            .opt_arg_index_key
            .switch_on_term_loc()
        {
            let clause_loc =
                find_inner_choice_instr(code, skeleton[clause_index].clause_start, index_loc);

            let target_indexing_line = code[target_index_loc].to_indexing_line_mut().unwrap();

            skeleton[clause_index]
                .opt_arg_index_key
                .set_switch_on_term_loc(target_index_loc);

            merge_clause_index(
                target_indexing_line,
                &mut skeleton[0..clause_index + 1],
                retracted_dynamic_clauses,
                clause_loc,
                AppendOrPrepend::Append,
            );

            retraction_info.push_record(RetractionRecord::AddedIndex(
                skeleton[clause_index].opt_arg_index_key.clone(),
                clause_loc,
            ));
        } else {
            break;
        }
    }
}

fn find_outer_choice_instr(code: &Code, mut index: usize) -> usize {
    loop {
        match &code[index] {
            Instruction::DynamicElse(_, _, NextOrFail::Next(i))
            | Instruction::DynamicInternalElse(_, _, NextOrFail::Next(i))
                if *i > 0 =>
            {
                index += i;
            }
            _ => {
                return index;
            }
        }
    }
}

fn find_inner_choice_instr(code: &Code, mut index: usize, index_loc: usize) -> usize {
    loop {
        match &code[index] {
            Instruction::TryMeElse(o) | Instruction::RetryMeElse(o) => {
                if *o > 0 {
                    return index;
                } else {
                    index = index_loc;
                }
            }
            &Instruction::DynamicElse(_, _, next_or_fail) => match next_or_fail {
                NextOrFail::Next(i) => {
                    if i == 0 {
                        index = index_loc;
                    } else {
                        return index;
                    }
                }
                NextOrFail::Fail(_) => {
                    index = index_loc;
                }
            },
            &Instruction::DynamicInternalElse(_, _, next_or_fail) => match next_or_fail {
                NextOrFail::Next(i) => {
                    if i == 0 {
                        index = index_loc;
                    } else {
                        return index;
                    }
                }
                NextOrFail::Fail(_) => {
                    return index;
                }
            },
            Instruction::TrustMe(_) => {
                return index;
            }
            Instruction::IndexingCode(indexing_code) => match &indexing_code[0] {
                IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(_, v, ..)) => match v {
                    IndexingCodePtr::External(v) => {
                        index += v;
                    }
                    IndexingCodePtr::DynamicExternal(v) => match &code[index + v] {
                        &Instruction::DynamicInternalElse(_, _, NextOrFail::Next(0)) => {
                            return index + v;
                        }
                        _ => {
                            index += v;
                        }
                    },
                    _ => unreachable!(),
                },
                _ => {
                    unreachable!();
                }
            },
            Instruction::RevJmpBy(offset) => {
                index -= offset;
            }
            _ => {
                /* Here we land at the line after a TryMeElse(0),
                 * which happens iff a single clause belongs to the
                 * indexed subsequence. So, end the search by pointing
                 * to the original derelict TryMeElse.
                 */
                return index - 1;
            }
        }
    }
}

fn remove_index_from_subsequence(
    code: &mut Code,
    opt_arg_index_key: &OptArgIndexKey,
    clause_start: usize,
    retraction_info: &mut RetractionInfo,
) {
    if let Some(index_loc) = opt_arg_index_key.switch_on_term_loc() {
        let clause_start = find_inner_choice_instr(code, clause_start, index_loc);
        let target_indexing_line = code[index_loc].to_indexing_line_mut().unwrap();
        let offset = clause_start - index_loc + 1;

        remove_index(opt_arg_index_key, target_indexing_line, offset);

        // TODO: this isn't sufficiently precise. The removed offset could
        // appear anywhere inside an Internal record.
        retraction_info.push_record(RetractionRecord::RemovedIndex(
            index_loc,
            opt_arg_index_key.clone(),
            offset,
        ));
    }
}

fn merge_indexed_subsequences(
    code: &mut Code,
    skeleton: &mut PredicateSkeleton,
    lower_upper_bound: usize,
    upper_lower_bound: usize,
    retraction_info: &mut RetractionInfo,
) -> Option<IndexPtr> {
    // patch the inner-threaded choice instructions to link the
    // two sequences, patch lower_bound's outer-threaded choice
    // instruction to TrustMe (or RetryMeElse), and derelict-ize
    // target_pos + 1's inner TryMeElse.

    let inner_trust_me_loc = skeleton.clauses[upper_lower_bound - 2].clause_start;

    let inner_try_me_else_loc = find_inner_choice_instr(
        code,
        skeleton.clauses[upper_lower_bound].clause_start,
        skeleton.clauses[upper_lower_bound]
            .opt_arg_index_key
            .switch_on_term_loc()
            .unwrap(),
    );

    if let Instruction::TryMeElse(ref mut o) = &mut code[inner_try_me_else_loc] {
        retraction_info.push_record(RetractionRecord::ModifiedTryMeElse(
            inner_try_me_else_loc,
            *o,
        ));

        match *o {
            0 => {
                code[inner_try_me_else_loc] = Instruction::TrustMe(0);
            }
            o => match &code[inner_try_me_else_loc + o] {
                Instruction::RevJmpBy(0) => {
                    code[inner_try_me_else_loc] = Instruction::TrustMe(o);
                }
                _ => {
                    code[inner_try_me_else_loc] = Instruction::RetryMeElse(o);
                }
            },
        }
    }

    thread_choice_instr_at_to(
        code,
        inner_trust_me_loc,
        inner_try_me_else_loc,
        retraction_info,
    );

    let mut end_of_upper_lower_bound = None;

    for index in upper_lower_bound..skeleton.clauses.len() {
        if !skeleton.clauses[index].opt_arg_index_key.is_some() {
            end_of_upper_lower_bound = Some(index);
            break;
        }
    }

    let outer_threaded_choice_instr_loc = skeleton.clauses[lower_upper_bound].clause_start - 2;

    match end_of_upper_lower_bound {
        Some(outer_threaded_clause_index) => {
            thread_choice_instr_at_to(
                code,
                outer_threaded_choice_instr_loc,
                skeleton.clauses[outer_threaded_clause_index].clause_start,
                retraction_info,
            );
        }
        None => {
            if let Instruction::TryMeElse(ref mut o) = &mut code[outer_threaded_choice_instr_loc] {
                retraction_info
                    .push_record(RetractionRecord::ModifiedTryMeElse(inner_trust_me_loc, *o));

                *o = 0;

                return Some(IndexPtr::index(outer_threaded_choice_instr_loc + 1));
            }
        }
    }

    None
}

fn delete_from_skeleton(
    compilation_target: CompilationTarget,
    key: PredicateKey,
    skeleton: &mut PredicateSkeleton,
    target_pos: usize,
    retraction_info: &mut RetractionInfo,
) -> usize {
    let clause_index_info = skeleton.clauses.remove(target_pos).unwrap();
    let clause_clause_loc = skeleton.core.clause_clause_locs.remove(target_pos).unwrap();

    if target_pos < skeleton.core.clause_assert_margin {
        skeleton.core.clause_assert_margin -= 1;
    }

    if skeleton.core.is_dynamic {
        skeleton
            .core
            .add_retracted_dynamic_clause_info(clause_index_info);

        retraction_info.push_record(RetractionRecord::RemovedDynamicSkeletonClause(
            compilation_target,
            key,
            target_pos,
            clause_clause_loc,
        ));
    } else {
        retraction_info.push_record(RetractionRecord::RemovedSkeletonClause(
            compilation_target,
            key,
            target_pos,
            clause_index_info,
            clause_clause_loc,
        ));
    }

    clause_clause_loc
}

fn blunt_leading_choice_instr(
    code: &mut Code,
    mut instr_loc: usize,
    retraction_info: &mut RetractionInfo,
) -> usize {
    loop {
        match &mut code[instr_loc] {
            Instruction::RetryMeElse(o) => {
                retraction_info.push_record(RetractionRecord::ModifiedRetryMeElse(instr_loc, *o));
                code[instr_loc] = Instruction::TryMeElse(*o);
                return instr_loc;
            }
            Instruction::DynamicElse(_, _, NextOrFail::Next(_))
            | Instruction::DynamicInternalElse(_, _, NextOrFail::Next(_)) => {
                return instr_loc;
            }
            &mut Instruction::DynamicElse(b, d, NextOrFail::Fail(o)) => {
                retraction_info.push_record(RetractionRecord::AppendedNextOrFail(
                    instr_loc,
                    NextOrFail::Fail(o),
                ));

                code[instr_loc] = Instruction::DynamicElse(b, d, NextOrFail::Next(0));
                return instr_loc;
            }
            &mut Instruction::DynamicInternalElse(b, d, NextOrFail::Fail(o)) => {
                retraction_info.push_record(RetractionRecord::AppendedNextOrFail(
                    instr_loc,
                    NextOrFail::Fail(o),
                ));

                code[instr_loc] = Instruction::DynamicInternalElse(b, d, NextOrFail::Next(0));

                return instr_loc;
            }
            Instruction::TrustMe(o) => {
                retraction_info
                    .push_record(RetractionRecord::AppendedTrustMe(instr_loc, *o, false));

                code[instr_loc] = Instruction::TryMeElse(0);
                return instr_loc + 1;
            }
            Instruction::TryMeElse(0) => {
                return instr_loc + 1;
            }
            Instruction::TryMeElse(o) => {
                instr_loc += *o;
            }
            Instruction::RevJmpBy(o) => {
                instr_loc -= *o;
            }
            _ => {
                unreachable!()
            }
        }
    }
}

fn set_switch_var_offset_to_choice_instr(
    code: &mut Code,
    index_loc: usize,
    offset: usize,
    retraction_info: &mut RetractionInfo,
) {
    let target_indexing_line = code[index_loc].to_indexing_line_mut().unwrap();

    let v = match &target_indexing_line[0] {
        &IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(_, v, ..)) => match v {
            IndexingCodePtr::External(v) | IndexingCodePtr::DynamicExternal(v) => v,
            _ => unreachable!(),
        },
        _ => {
            unreachable!();
        }
    };

    match &code[index_loc + v] {
        Instruction::TryMeElse(_)
        | Instruction::DynamicElse(..)
        | Instruction::DynamicInternalElse(..) => {}
        _ => {
            set_switch_var_offset(code, index_loc, offset, retraction_info);
        }
    }
}

#[inline]
fn set_switch_var_offset(
    code: &mut Code,
    index_loc: usize,
    offset: usize,
    retraction_info: &mut RetractionInfo,
) {
    let target_indexing_line = code[index_loc].to_indexing_line_mut().unwrap();

    let old_v = match &mut target_indexing_line[0] {
        IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(_, ref mut v, ..)) => match *v {
            IndexingCodePtr::DynamicExternal(_) => {
                mem::replace(v, IndexingCodePtr::DynamicExternal(offset))
            }
            IndexingCodePtr::External(_) => mem::replace(v, IndexingCodePtr::External(offset)),
            _ => unreachable!(),
        },
        _ => {
            unreachable!()
        }
    };

    retraction_info.push_record(RetractionRecord::ReplacedSwitchOnTermVarIndex(
        index_loc, old_v,
    ));
}

fn internalize_choice_instr_at(
    code: &mut Code,
    instr_loc: usize,
    retraction_info: &mut RetractionInfo,
) {
    match &mut code[instr_loc] {
        Instruction::DynamicElse(_, _, NextOrFail::Fail(_))
        | Instruction::DynamicInternalElse(_, _, NextOrFail::Fail(_)) => {}
        Instruction::DynamicElse(_, _, ref mut o @ NextOrFail::Next(0)) => {
            retraction_info.push_record(RetractionRecord::ReplacedDynamicElseOffset(instr_loc, 0));
            *o = NextOrFail::Fail(0);
        }
        &mut Instruction::DynamicElse(b, d, NextOrFail::Next(o)) => {
            retraction_info.push_record(RetractionRecord::AppendedNextOrFail(
                instr_loc,
                NextOrFail::Next(o),
            ));

            match &mut code[instr_loc + o] {
                Instruction::RevJmpBy(p) if *p == 0 => {
                    code[instr_loc] = Instruction::DynamicElse(b, d, NextOrFail::Fail(o));
                }
                _ => {
                    code[instr_loc] = Instruction::DynamicElse(b, d, NextOrFail::Next(o));
                }
            }
        }
        Instruction::DynamicInternalElse(_, _, ref mut o @ NextOrFail::Next(0)) => {
            retraction_info.push_record(RetractionRecord::ReplacedDynamicElseOffset(instr_loc, 0));
            *o = NextOrFail::Fail(0);
        }
        &mut Instruction::DynamicInternalElse(b, d, NextOrFail::Next(o)) => {
            retraction_info.push_record(RetractionRecord::ReplacedDynamicElseOffset(instr_loc, o));

            match &mut code[instr_loc + o] {
                Instruction::RevJmpBy(p) if *p == 0 => {
                    code[instr_loc] = Instruction::DynamicInternalElse(b, d, NextOrFail::Fail(o));
                }
                _ => {
                    code[instr_loc] = Instruction::DynamicInternalElse(b, d, NextOrFail::Next(o));
                }
            }
        }
        Instruction::TryMeElse(0) => {
            retraction_info.push_record(RetractionRecord::ModifiedTryMeElse(instr_loc, 0));
            code[instr_loc] = Instruction::TrustMe(0);
        }
        Instruction::TryMeElse(o) => {
            let o = *o;

            retraction_info.push_record(RetractionRecord::ModifiedTryMeElse(instr_loc, o));

            match &mut code[instr_loc + o] {
                Instruction::RevJmpBy(p) if *p == 0 => {
                    code[instr_loc] = Instruction::TrustMe(o);
                }
                _ => {
                    code[instr_loc] = Instruction::RetryMeElse(o);
                }
            }
        }
        _ => {
            unreachable!();
        }
    }
}

fn thread_choice_instr_at_to(
    code: &mut Code,
    mut instr_loc: usize,
    target_loc: usize,
    retraction_info: &mut RetractionInfo,
) {
    loop {
        match &mut code[instr_loc] {
            Instruction::TryMeElse(ref mut o) | Instruction::RetryMeElse(ref mut o)
                if target_loc >= instr_loc =>
            {
                retraction_info.push_record(RetractionRecord::ReplacedChoiceOffset(instr_loc, *o));

                *o = target_loc - instr_loc;
                return;
            }
            Instruction::DynamicElse(_, _, NextOrFail::Next(ref mut o))
            | Instruction::DynamicInternalElse(_, _, NextOrFail::Next(ref mut o))
                if target_loc >= instr_loc =>
            {
                retraction_info
                    .push_record(RetractionRecord::ReplacedDynamicElseOffset(instr_loc, *o));
                *o = target_loc - instr_loc;
                return;
            }
            Instruction::DynamicElse(_, _, NextOrFail::Next(o))
            | Instruction::DynamicInternalElse(_, _, NextOrFail::Next(o)) => {
                instr_loc += *o;
            }
            Instruction::TryMeElse(o) | Instruction::RetryMeElse(o) => {
                instr_loc += *o;
            }
            Instruction::RevJmpBy(ref mut o) if instr_loc >= target_loc => {
                retraction_info.push_record(RetractionRecord::ModifiedRevJmpBy(instr_loc, *o));

                *o = instr_loc - target_loc;
                return;
            }
            &mut Instruction::RevJmpBy(o) => {
                instr_loc -= o;
            }
            &mut Instruction::DynamicElse(birth, death, ref mut fail)
                if target_loc >= instr_loc =>
            {
                retraction_info.push_record(RetractionRecord::AppendedNextOrFail(instr_loc, *fail));

                code[instr_loc] = instr!(
                    "dynamic_else",
                    birth,
                    death,
                    NextOrFail::Next(target_loc - instr_loc)
                );

                return;
            }
            Instruction::DynamicElse(_, _, NextOrFail::Fail(o)) if *o > 0 => {
                instr_loc += *o;
            }
            &mut Instruction::DynamicInternalElse(birth, death, ref mut fail)
                if target_loc >= instr_loc =>
            {
                retraction_info.push_record(RetractionRecord::AppendedNextOrFail(instr_loc, *fail));

                code[instr_loc] = instr!(
                    "dynamic_internal_else",
                    birth,
                    death,
                    NextOrFail::Next(target_loc - instr_loc)
                );

                return;
            }
            Instruction::DynamicInternalElse(_, _, NextOrFail::Fail(o)) if *o > 0 => {
                instr_loc += *o;
            }
            Instruction::TrustMe(ref mut o) if target_loc >= instr_loc => {
                retraction_info.push_record(
                    RetractionRecord::AppendedTrustMe(instr_loc, *o, false),
                    //choice_instr.is_default()),
                );

                code[instr_loc] = instr!("retry_me_else", target_loc - instr_loc);
                return;
            }
            Instruction::TrustMe(o) if *o > 0 => {
                instr_loc += *o;
            }
            _ => {
                unreachable!()
            }
        }
    }
}

fn remove_non_leading_clause(
    code: &mut Code,
    preceding_choice_instr_loc: usize,
    non_indexed_choice_instr_loc: usize,
    retraction_info: &mut RetractionInfo,
) -> Option<IndexPtr> {
    match &mut code[non_indexed_choice_instr_loc] {
        Instruction::RetryMeElse(ref mut o) => {
            let o = *o;

            thread_choice_instr_at_to(
                code,
                preceding_choice_instr_loc,
                non_indexed_choice_instr_loc + o,
                retraction_info,
            );

            None
        }
        Instruction::TrustMe(_) => match &mut code[preceding_choice_instr_loc] {
            Instruction::RetryMeElse(o) => {
                retraction_info.push_record(RetractionRecord::ModifiedRetryMeElse(
                    preceding_choice_instr_loc,
                    *o,
                ));

                code[preceding_choice_instr_loc] = Instruction::TrustMe(0);

                None
            }
            Instruction::TryMeElse(ref mut o) => {
                retraction_info.push_record(RetractionRecord::ModifiedTryMeElse(
                    preceding_choice_instr_loc,
                    *o,
                ));

                *o = 0;

                Some(IndexPtr::index(preceding_choice_instr_loc + 1))
            }
            _ => {
                unreachable!();
            }
        },
        _ => {
            unreachable!();
        }
    }
}

fn finalize_retract(
    key: PredicateKey,
    compilation_target: CompilationTarget,
    skeleton: &mut PredicateSkeleton,
    code_index: CodeIndex,
    target_pos: usize,
    index_ptr_opt: Option<IndexPtr>,
    retraction_info: &mut RetractionInfo,
) -> usize {
    let clause_clause_loc = delete_from_skeleton(
        compilation_target,
        key,
        skeleton,
        target_pos,
        retraction_info,
    );

    if let Some(index_ptr) = index_ptr_opt {
        set_code_index(
            retraction_info,
            &compilation_target,
            key,
            code_index,
            index_ptr,
        );
    }

    clause_clause_loc
}

fn remove_leading_unindexed_clause(
    code: &mut Code,
    non_indexed_choice_instr_loc: usize,
    retraction_info: &mut RetractionInfo,
) -> Option<IndexPtr> {
    match &mut code[non_indexed_choice_instr_loc] {
        Instruction::TryMeElse(ref mut o) => {
            if *o > 0 {
                retraction_info.push_record(RetractionRecord::ModifiedTryMeElse(
                    non_indexed_choice_instr_loc,
                    *o,
                ));

                let o = mem::replace(o, 0);

                let index_ptr = blunt_leading_choice_instr(
                    code,
                    non_indexed_choice_instr_loc + o,
                    retraction_info,
                );

                Some(IndexPtr::index(index_ptr))
            } else {
                Some(IndexPtr::dynamic_undefined())
            }
        }
        _ => {
            unreachable!();
        }
    }
}

fn find_dynamic_outer_choice_instr(code: &Code, index_loc: usize) -> usize {
    match &code[index_loc] {
        Instruction::IndexingCode(indexing_code) => match &indexing_code[0] {
            &IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(
                _,
                IndexingCodePtr::DynamicExternal(v),
                ..,
            )) => index_loc + v - 2,
            _ => unreachable!(),
        },
        _ => unreachable!(),
    }
}

fn prepend_compiled_clause(
    code: &mut Code,
    compilation_target: CompilationTarget,
    key: PredicateKey,
    mut clause_code: Code,
    skeleton: &mut PredicateSkeleton,
    retraction_info: &mut RetractionInfo,
    global_clock_tick: usize,
) -> IndexPtr {
    let clause_loc = code.len();
    let mut prepend_queue = VecDeque::new();

    let target_arg_num = skeleton.clauses[0].opt_arg_index_key.arg_num();
    let head_arg_num = skeleton.clauses[1].opt_arg_index_key.arg_num();

    let settings = CodeGenSettings {
        global_clock_tick: if skeleton.core.is_dynamic {
            Some(global_clock_tick)
        } else {
            None
        },
        is_extensible: true,
        non_counted_bt: false,
    };

    let clause_loc = if skeleton.clauses[0]
        .opt_arg_index_key
        .switch_on_term_loc()
        .is_some()
    {
        match skeleton.clauses[1].opt_arg_index_key.switch_on_term_loc() {
            Some(index_loc) if target_arg_num == head_arg_num => {
                prepend_queue.extend(clause_code.drain(3..));

                skeleton.clauses[0].opt_arg_index_key += index_loc - 1;
                skeleton.clauses[0].clause_start = clause_loc + 2;

                retraction_info.push_record(RetractionRecord::AddedIndex(
                    skeleton.clauses[0].opt_arg_index_key.clone(),
                    skeleton.clauses[0].clause_start,
                ));

                let outer_thread_choice_loc = if skeleton.core.is_dynamic {
                    find_dynamic_outer_choice_instr(code, index_loc)
                } else {
                    skeleton.clauses[1].clause_start - 2
                };

                retraction_info.push_record(RetractionRecord::SkeletonClauseStartReplaced(
                    compilation_target,
                    key,
                    1,
                    skeleton.clauses[1].clause_start,
                ));

                skeleton.clauses[1].clause_start =
                    find_inner_choice_instr(code, skeleton.clauses[1].clause_start, index_loc);

                let inner_thread_rev_offset =
                    3 + prepend_queue.len() + clause_loc - skeleton.clauses[1].clause_start;

                prepend_queue.push_back(Instruction::RevJmpBy(inner_thread_rev_offset));

                prepend_queue.push_front(settings.internal_try_me_else(prepend_queue.len()));

                // prepend_queue is now:
                //      | TryMeElse N_2
                //      | (clause_code)
                // +N_2 | RevJmpBy (RetryMeElse(M_1) or TryMeElse(0) at index_loc + 1)

                prepend_queue.push_front(Instruction::RevJmpBy(1 + clause_loc - index_loc));

                let outer_thread_choice_offset = // outer_thread_choice_loc WAS index_loc - 1..
                    match derelictize_try_me_else(code, outer_thread_choice_loc, retraction_info) {
                        Some(next_subseq_offset) => {
                            // skeleton.clauses[1] has a non-stub TryMeElse.

                            let outer_thread_rev_offset =
                                prepend_queue.len() + 1 + clause_loc - outer_thread_choice_loc -
                                next_subseq_offset;

                            prepend_queue.push_back(
                                Instruction::RevJmpBy(outer_thread_rev_offset)
                            );

                            prepend_queue.len()
                        }
                        None => {
                            // This case occurs when the clauses of
                            // the host predicate, up to and including
                            // the prepending of this clause, are
                            // indexed.

                            // The outer TryMeElse / RevJmpBy pushed
                            // in this case are stub instructions
                            // awaiting the addition of unindexed
                            // clauses.

                            prepend_queue.push_back(Instruction::RevJmpBy(0));

                            0
                        }
                    };

                prepend_queue.push_front(settings.try_me_else(outer_thread_choice_offset));

                // prepend_queue is now:
                //     | TryMeElse N_3
                //     | RevJmpBy (SwitchOnTerm at index_loc)
                //     | TryMeElse N_2
                //     | (clause_code)
                // N_2 | RevJmpBy (RetryMeElse(M_1) or TryMeElse(0) at index_loc + 1)
                // N_3 | RevJmpBy (TryMeElse(N_1) at index_loc - 1 or TrustMe if N_1 == 0)

                let target_indexing_line = code[index_loc].to_indexing_line_mut().unwrap();

                merge_clause_index(
                    target_indexing_line,
                    skeleton.clauses.make_contiguous(),
                    &skeleton.core.retracted_dynamic_clauses,
                    clause_loc + 2, // == skeleton.clauses[0].clause_start
                    AppendOrPrepend::Prepend,
                );

                set_switch_var_offset(code, index_loc, clause_loc - index_loc + 2, retraction_info);

                internalize_choice_instr_at(
                    code,
                    skeleton.clauses[1].clause_start,
                    retraction_info,
                );

                code.extend(prepend_queue);

                if skeleton.core.is_dynamic {
                    clause_loc
                } else {
                    clause_loc + (outer_thread_choice_offset == 0) as usize
                }
            }
            _ => {
                prepend_queue.extend(clause_code.drain(1..));

                skeleton.clauses[0].opt_arg_index_key += clause_loc;
                skeleton.clauses[0].clause_start = clause_loc + 2;

                let old_clause_start =
                    match skeleton.clauses[1].opt_arg_index_key.switch_on_term_loc() {
                        Some(index_loc) if skeleton.core.is_dynamic => {
                            find_dynamic_outer_choice_instr(code, index_loc)
                        }
                        Some(_) => skeleton.clauses[1].clause_start - 2,
                        None => skeleton.clauses[1].clause_start,
                    };

                let inner_thread_rev_offset =
                    2 + prepend_queue.len() + clause_loc - old_clause_start;

                // this is a stub for chaining inner-threaded choice
                // instructions.
                prepend_queue.push_back(Instruction::RevJmpBy(0));

                let prepend_queue_len = prepend_queue.len();

                match &mut prepend_queue[1] {
                    Instruction::TryMeElse(ref mut o) if *o == 0 => {
                        *o = prepend_queue_len - 2;
                    }
                    Instruction::DynamicInternalElse(_, _, ref mut o @ NextOrFail::Next(0)) => {
                        *o = NextOrFail::Fail(prepend_queue_len - 2);
                    }
                    _ => {
                        unreachable!();
                    }
                }

                prepend_queue.push_back(Instruction::RevJmpBy(inner_thread_rev_offset));
                prepend_queue.push_front(settings.try_me_else(prepend_queue.len()));

                // prepend_queue is now:
                //      | TryMeElse(N_2)
                //      | SwitchOnTerm 2, ...
                //      | TryMeElse(0)
                //      | (clause_code)
                // +N_2 | RevJmpBy (RetryMeElse(M_1))

                internalize_choice_instr_at(code, old_clause_start, retraction_info);

                code.extend(prepend_queue);

                clause_loc // + (outer_thread_choice_offset == 0 as usize)
            }
        }
    } else {
        match skeleton.clauses[1].opt_arg_index_key.switch_on_term_loc() {
            Some(index_loc) => {
                prepend_queue.extend(clause_code.drain(1..));

                let old_clause_start = if skeleton.core.is_dynamic {
                    find_dynamic_outer_choice_instr(code, index_loc)
                } else {
                    skeleton.clauses[1].clause_start - 2
                };

                let inner_thread_rev_offset =
                    1 + prepend_queue.len() + clause_loc - old_clause_start;

                prepend_queue.push_back(Instruction::RevJmpBy(inner_thread_rev_offset));
                prepend_queue.push_front(settings.try_me_else(prepend_queue.len()));

                // prepend_queue is now:
                //      | TryMeElse(N_2)
                //      | (clause_code)
                // +N_2 | RevJmpBy (RetryMeElse(M_1))

                internalize_choice_instr_at(code, old_clause_start, retraction_info);

                code.extend(prepend_queue);

                // skeleton.clauses[0].opt_arg_index_key += clause_loc;
                skeleton.clauses[0].clause_start = clause_loc;

                clause_loc // + (outer_thread_choice_offset == 0 as usize)
            }
            None => {
                prepend_queue.extend(clause_code.drain(1..));

                let old_clause_start = skeleton.clauses[1].clause_start;

                let inner_thread_rev_offset =
                    1 + prepend_queue.len() + clause_loc - old_clause_start;

                prepend_queue.push_back(Instruction::RevJmpBy(inner_thread_rev_offset));
                prepend_queue.push_front(settings.try_me_else(prepend_queue.len()));

                // prepend_queue is now:
                //      | TryMeElse(N_2)
                //      | (clause_code)
                // +N_2 | RevJmpBy (RetryMeElse(M_1))

                internalize_choice_instr_at(code, old_clause_start, retraction_info);

                code.extend(prepend_queue);

                // skeleton.clauses[0].opt_arg_index_key += clause_loc;
                skeleton.clauses[0].clause_start = clause_loc;

                clause_loc
            }
        }
    };

    if skeleton.core.is_dynamic {
        IndexPtr::dynamic_index(clause_loc)
    } else {
        IndexPtr::index(clause_loc)
    }
}

fn append_compiled_clause(
    code: &mut Code,
    mut clause_code: Code,
    skeleton: &mut PredicateSkeleton,
    retraction_info: &mut RetractionInfo,
    global_clock_tick: usize,
) -> Option<IndexPtr> {
    let clause_loc = code.len();
    let target_pos = skeleton.clauses.len() - 1;
    let lower_bound = lower_bound_of_target_clause(skeleton, target_pos);

    let settings = CodeGenSettings {
        global_clock_tick: if skeleton.core.is_dynamic {
            Some(global_clock_tick)
        } else {
            None
        },
        is_extensible: true,
        non_counted_bt: false,
    };

    skeleton.clauses[target_pos].clause_start = clause_loc;

    let mut code_ptr_opt = None;

    let lower_bound_arg_num = skeleton.clauses[lower_bound].opt_arg_index_key.arg_num();
    let target_arg_num = skeleton.clauses[target_pos].opt_arg_index_key.arg_num();

    let threaded_choice_instr_loc = match skeleton.clauses[lower_bound]
        .opt_arg_index_key
        .switch_on_term_loc()
    {
        Some(index_loc) if lower_bound_arg_num == target_arg_num => {
            code.push(settings.internal_trust_me());
            code.extend(clause_code.drain(3..)); // skip the indexing code

            // set skeleton[target_pos].opt_arg_index_key to
            // index_loc. its original value is always 1.
            skeleton.clauses[target_pos].opt_arg_index_key += index_loc - 1;

            retraction_info.push_record(RetractionRecord::AddedIndex(
                skeleton.clauses[target_pos].opt_arg_index_key.clone(),
                skeleton.clauses[target_pos].clause_start,
            ));

            let target_indexing_line = code[index_loc].to_indexing_line_mut().unwrap();

            merge_clause_index(
                target_indexing_line,
                &mut skeleton.clauses.make_contiguous()[lower_bound..],
                &skeleton.core.retracted_dynamic_clauses,
                clause_loc,
                AppendOrPrepend::Append,
            );

            let target_pos_clause_start = find_inner_choice_instr(
                code,
                skeleton.clauses[target_pos - 1].clause_start,
                index_loc,
            );

            let target_pos_clause_start = find_outer_choice_instr(code, target_pos_clause_start);

            if lower_bound + 1 == target_pos {
                set_switch_var_offset_to_choice_instr(
                    code,
                    index_loc,
                    target_pos_clause_start - index_loc,
                    retraction_info,
                );

                if lower_bound == 0 && !skeleton.core.is_dynamic {
                    code_ptr_opt = Some(if index_loc < target_pos_clause_start {
                        index_loc
                    } else {
                        target_pos_clause_start
                    });
                }
            }

            target_pos_clause_start // skeleton.clauses[target_pos - 1].clause_start
        }
        _ => {
            code.push(settings.trust_me());

            skeleton.clauses[target_pos].opt_arg_index_key += clause_loc;
            code.extend(clause_code.drain(1..));

            if let Some(index_loc) = skeleton.clauses[target_pos]
                .opt_arg_index_key
                .switch_on_term_loc()
            {
                // point to the inner-threaded TryMeElse(0) if target_pos is
                // indexed, and make switch_on_term point one line after it in
                // its variable offset.
                skeleton.clauses[target_pos].clause_start += 2;

                if !skeleton.core.is_dynamic {
                    set_switch_var_offset(code, index_loc, 2, retraction_info);
                }
            }

            match skeleton.clauses[lower_bound]
                .opt_arg_index_key
                .switch_on_term_loc()
            {
                Some(_) => {
                    if lower_bound == 0 {
                        code_ptr_opt = Some(skeleton.clauses[lower_bound].clause_start - 2);
                    }

                    find_outer_choice_instr(code, skeleton.clauses[lower_bound].clause_start - 2)
                }
                None => {
                    if lower_bound == 0 {
                        code_ptr_opt = Some(skeleton.clauses[lower_bound].clause_start);
                    }

                    find_outer_choice_instr(code, skeleton.clauses[lower_bound].clause_start)
                }
            }
        }
    };

    thread_choice_instr_at_to(code, threaded_choice_instr_loc, clause_loc, retraction_info);

    code_ptr_opt.map(|p| {
        if skeleton.core.is_dynamic {
            IndexPtr::dynamic_index(p)
        } else {
            IndexPtr::index(p)
        }
    })
}

#[inline]
fn mergeable_indexed_subsequences(
    lower_bound: usize,
    target_pos: usize,
    skeleton: &PredicateSkeleton,
) -> bool {
    let lower_bound_arg_num = skeleton.clauses[lower_bound].opt_arg_index_key.arg_num();

    if target_pos + 1 < skeleton.clauses.len() {
        let succ_arg_num = skeleton.clauses[target_pos + 1].opt_arg_index_key.arg_num();
        let target_arg_num = skeleton.clauses[target_pos].opt_arg_index_key.arg_num();

        return target_arg_num != succ_arg_num && lower_bound_arg_num == succ_arg_num;
    }

    false
}

fn print_overwrite_warning(
    compilation_target: &CompilationTarget,
    code_ptr: IndexPtr,
    key: PredicateKey,
    is_dynamic: bool,
) {
    if let CompilationTarget::Module(module_name) = compilation_target {
        match module_name {
            atom!("builtins") | atom!("loader") => return,
            _ => {}
        }
    }

    match code_ptr.tag() {
        IndexPtrTag::DynamicUndefined | IndexPtrTag::Undefined => return,
        _ if is_dynamic => return,
        _ => {}
    }

    println!(
        "Warning: overwriting {}/{} because the clauses are discontiguous",
        key.0.as_str(),
        key.1
    );
}

impl<'a, LS: LoadState<'a>> Loader<'a, LS> {
    pub(super) fn listing_src_file_name(&mut self) -> Option<Atom> {
        if let Some(load_context) = self.wam_prelude.load_contexts.last() {
            if !load_context.path.is_file() {
                return None;
            }

            if let Some(path_str) = load_context.path.to_str() {
                if !path_str.is_empty() {
                    return Some(AtomTable::build_with(
                        &LS::machine_st(&mut self.payload).atom_tbl,
                        path_str,
                    ));
                }
            }
        }

        None
    }

    fn compile_standalone_clause(
        &mut self,
        term: Term,
        settings: CodeGenSettings,
    ) -> Result<StandaloneCompileResult, SessionError> {
        let mut preprocessor = Preprocessor::new(settings);

        let clause = self.try_term_to_tl(term, &mut preprocessor)?;
        // let queue = preprocessor.parse_queue(self)?;

        let mut cg = CodeGenerator::new(&LS::machine_st(&mut self.payload).atom_tbl, settings);

        let clause_code = cg.compile_predicate(vec![clause])?;

        Ok(StandaloneCompileResult {
            clause_code,
            standalone_skeleton: cg.skeleton,
        })
    }

    fn compile(
        &mut self,
        key: PredicateKey,
        mut predicates: PredicateQueue,
        settings: CodeGenSettings,
    ) -> Result<CodeIndex, SessionError> {
        let code_index = self.get_or_insert_code_index(key, predicates.compilation_target);

        LS::err_on_builtin_overwrite(self, key)?;

        let code_len = self.wam_prelude.code.len();
        let mut code_ptr = code_len;

        let mut clauses = vec![];
        let mut preprocessor = Preprocessor::new(settings);

        for term in predicates.predicates.drain(0..) {
            clauses.push(self.try_term_to_tl(term, &mut preprocessor)?);
        }

        let mut cg = CodeGenerator::new(&LS::machine_st(&mut self.payload).atom_tbl, settings);

        let mut code = cg.compile_predicate(clauses)?;

        if settings.is_extensible {
            let mut clause_clause_locs = VecDeque::new();

            for clause_index_info in cg.skeleton.clauses.iter_mut() {
                clause_index_info.clause_start += code_len;
                clause_index_info.opt_arg_index_key += code_len;

                clause_clause_locs.push_back(clause_index_info.clause_start);
            }

            if let Instruction::TryMeElse(0) = &mut code[0] {
                code_ptr += 1;
            }

            match self
                .wam_prelude
                .indices
                .get_predicate_skeleton_mut(&predicates.compilation_target, &key)
            {
                Some(skeleton) => {
                    let skeleton_clause_len = skeleton.clauses.len();

                    skeleton.clauses.extend(cg.skeleton.clauses);
                    skeleton
                        .core
                        .clause_clause_locs
                        .extend(&clause_clause_locs.make_contiguous()[0..]);

                    self.payload.retraction_info.push_record(
                        RetractionRecord::SkeletonClauseTruncateBack(
                            predicates.compilation_target,
                            key,
                            skeleton_clause_len,
                        ),
                    );
                }
                None => {
                    cg.skeleton
                        .core
                        .clause_clause_locs
                        .extend(&clause_clause_locs.make_contiguous()[0..]);

                    let skeleton = cg.skeleton;

                    self.add_extensible_predicate(key, skeleton, predicates.compilation_target);
                }
            };

            self.extend_local_predicate_skeleton(
                &predicates.compilation_target,
                &key,
                clause_clause_locs,
            );
        }

        print_overwrite_warning(
            &predicates.compilation_target,
            code_index.get(),
            key,
            settings.is_dynamic(),
        );

        let index_ptr = if settings.is_dynamic() {
            IndexPtr::dynamic_index(code_ptr)
        } else {
            IndexPtr::index(code_ptr)
        };

        set_code_index(
            &mut self.payload.retraction_info,
            &predicates.compilation_target,
            key,
            code_index,
            index_ptr,
        );

        self.wam_prelude.code.extend(code);
        Ok(code_index)
    }

    fn extend_local_predicate_skeleton(
        &mut self,
        compilation_target: &CompilationTarget,
        key: &PredicateKey,
        mut clause_clause_locs: VecDeque<usize>,
    ) {
        let listing_src_file_name = self.listing_src_file_name();

        match self.wam_prelude.indices.get_local_predicate_skeleton_mut(
            self.payload.compilation_target,
            *compilation_target,
            listing_src_file_name,
            *key,
        ) {
            Some(skeleton) => {
                let payload_compilation_target = self.payload.compilation_target;

                self.payload.retraction_info.push_record(
                    RetractionRecord::SkeletonLocalClauseTruncateBack(
                        payload_compilation_target,
                        *compilation_target,
                        *key,
                        skeleton.clause_clause_locs.len(),
                    ),
                );

                skeleton
                    .clause_clause_locs
                    .extend(&clause_clause_locs.make_contiguous()[0..]);
            }
            None => {
                let mut skeleton = LocalPredicateSkeleton::new();
                skeleton.clause_clause_locs = clause_clause_locs;

                self.add_local_extensible_predicate(*compilation_target, *key, skeleton);
            }
        }
    }

    fn push_front_to_local_predicate_skeleton(
        &mut self,
        compilation_target: &CompilationTarget,
        key: &PredicateKey,
        code_len: usize,
    ) {
        let listing_src_file_name = self.listing_src_file_name();

        match self.wam_prelude.indices.get_local_predicate_skeleton_mut(
            self.payload.compilation_target,
            *compilation_target,
            listing_src_file_name,
            *key,
        ) {
            Some(skeleton) => {
                let payload_compilation_target = self.payload.compilation_target;

                self.payload.retraction_info.push_record(
                    RetractionRecord::SkeletonLocalClauseClausePopFront(
                        payload_compilation_target,
                        *compilation_target,
                        *key,
                    ),
                );

                skeleton.clause_clause_locs.push_front(code_len);
            }
            None => {
                let mut skeleton = LocalPredicateSkeleton::new();
                skeleton.clause_clause_locs.push_front(code_len);

                self.add_local_extensible_predicate(*compilation_target, *key, skeleton);
            }
        }
    }

    fn push_back_to_local_predicate_skeleton(
        &mut self,
        compilation_target: &CompilationTarget,
        key: &PredicateKey,
        code_len: usize,
    ) {
        let listing_src_file_name = self.listing_src_file_name();

        match self.wam_prelude.indices.get_local_predicate_skeleton_mut(
            self.payload.compilation_target,
            *compilation_target,
            listing_src_file_name,
            *key,
        ) {
            Some(skeleton) => {
                let payload_compilation_target = self.payload.compilation_target;

                self.payload.retraction_info.push_record(
                    RetractionRecord::SkeletonLocalClauseClausePopBack(
                        payload_compilation_target,
                        *compilation_target,
                        *key,
                    ),
                );

                skeleton.clause_clause_locs.push_back(code_len);
            }
            None => {
                let mut skeleton = LocalPredicateSkeleton::new();
                skeleton.clause_clause_locs.push_back(code_len);

                self.add_local_extensible_predicate(*compilation_target, *key, skeleton);
            }
        }
    }

    pub(super) fn incremental_compile_clause(
        &mut self,
        key: PredicateKey,
        clause: Term,
        compilation_target: CompilationTarget,
        non_counted_bt: bool,
        append_or_prepend: AppendOrPrepend,
    ) -> Result<CodeIndex, SessionError> {
        let settings = match self
            .wam_prelude
            .indices
            .get_predicate_skeleton_mut(&compilation_target, &key)
        {
            Some(skeleton) if !skeleton.clauses.is_empty() => CodeGenSettings {
                global_clock_tick: if skeleton.core.is_dynamic {
                    Some(LS::machine_st(&mut self.payload).global_clock)
                } else {
                    None
                },
                is_extensible: true,
                non_counted_bt,
            },
            skeleton_opt => {
                let settings = CodeGenSettings {
                    global_clock_tick: if let Some(skeleton) = skeleton_opt {
                        if skeleton.core.is_dynamic {
                            Some(LS::machine_st(&mut self.payload).global_clock)
                        } else {
                            None
                        }
                    } else {
                        None
                    },
                    is_extensible: true,
                    non_counted_bt,
                };

                let mut predicate_queue = predicate_queue![clause];
                predicate_queue.compilation_target = compilation_target;

                return self.compile(key, predicate_queue, settings);
            }
        };

        let StandaloneCompileResult {
            clause_code,
            mut standalone_skeleton,
        } = self.compile_standalone_clause(clause, settings)?;

        let code_len = self.wam_prelude.code.len();

        let skeleton = match self
            .wam_prelude
            .indices
            .get_predicate_skeleton_mut(&compilation_target, &key)
        {
            Some(skeleton) if !skeleton.clauses.is_empty() => skeleton,
            _ => unreachable!(),
        };

        match append_or_prepend {
            AppendOrPrepend::Append => {
                let clause_index_info = standalone_skeleton.clauses.pop_back().unwrap();
                skeleton.clauses.push_back(clause_index_info);

                skeleton.core.clause_clause_locs.push_back(code_len);

                self.payload
                    .retraction_info
                    .push_record(RetractionRecord::SkeletonClausePopBack(
                        compilation_target,
                        key,
                    ));

                let global_clock = LS::machine_st(&mut self.payload).global_clock;

                let result = append_compiled_clause(
                    self.wam_prelude.code,
                    clause_code,
                    skeleton,
                    &mut self.payload.retraction_info,
                    global_clock,
                );

                self.push_back_to_local_predicate_skeleton(&compilation_target, &key, code_len);

                let code_index = self.get_or_insert_code_index(key, compilation_target);

                if let Some(new_code_ptr) = result {
                    set_code_index(
                        &mut self.payload.retraction_info,
                        &compilation_target,
                        key,
                        code_index,
                        new_code_ptr,
                    );
                }

                Ok(code_index)
            }
            AppendOrPrepend::Prepend => {
                let clause_index_info = standalone_skeleton.clauses.pop_back().unwrap();
                skeleton.clauses.push_front(clause_index_info);

                skeleton.core.clause_clause_locs.push_front(code_len);
                skeleton.core.clause_assert_margin += 1;

                self.payload
                    .retraction_info
                    .push_record(RetractionRecord::SkeletonClausePopFront(
                        compilation_target,
                        key,
                    ));

                let global_clock = LS::machine_st(&mut self.payload).global_clock;

                let new_code_ptr = prepend_compiled_clause(
                    self.wam_prelude.code,
                    compilation_target,
                    key,
                    clause_code,
                    skeleton,
                    &mut self.payload.retraction_info,
                    global_clock,
                );

                self.push_front_to_local_predicate_skeleton(&compilation_target, &key, code_len);

                let code_index = self.get_or_insert_code_index(key, compilation_target);

                set_code_index(
                    &mut self.payload.retraction_info,
                    &compilation_target,
                    key,
                    code_index,
                    new_code_ptr,
                );

                Ok(code_index)
            }
        }
    }

    pub(super) fn retract_dynamic_clause(&mut self, key: PredicateKey, target_pos: usize) -> usize {
        let skeleton = match self
            .wam_prelude
            .indices
            .get_predicate_skeleton_mut(&self.payload.compilation_target, &key)
        {
            Some(skeleton) => skeleton,
            None => {
                unreachable!();
            }
        };

        let clause_loc = match skeleton.clauses[target_pos]
            .opt_arg_index_key
            .switch_on_term_loc()
        {
            Some(index_loc) => find_inner_choice_instr(
                self.wam_prelude.code,
                skeleton.clauses[target_pos].clause_start,
                index_loc,
            ),
            None => skeleton.clauses[target_pos].clause_start,
        };

        match &mut self.wam_prelude.code[clause_loc] {
            Instruction::DynamicElse(_, ref mut d, _)
            | Instruction::DynamicInternalElse(_, ref mut d, _) => {
                *d = Death::Finite(LS::machine_st(&mut self.payload).global_clock);
            }
            _ => unreachable!(),
        }

        delete_from_skeleton(
            self.payload.compilation_target,
            key,
            skeleton,
            target_pos,
            &mut self.payload.retraction_info,
        )
    }

    pub(super) fn retract_clause(&mut self, key: PredicateKey, target_pos: usize) -> usize {
        let payload_compilation_target = self.payload.compilation_target;
        let code_index = self.get_or_insert_code_index(key, payload_compilation_target);

        let skeleton = self
            .wam_prelude
            .indices
            .get_predicate_skeleton_mut(&payload_compilation_target, &key)
            .unwrap();

        let code = &mut self.wam_prelude.code;
        let lower_bound = lower_bound_of_target_clause(skeleton, target_pos);
        let lower_bound_is_unindexed = !skeleton.clauses[lower_bound].opt_arg_index_key.is_some();

        if target_pos == 0 || (lower_bound + 1 == target_pos && lower_bound_is_unindexed) {
            // the clause preceding target_pos, if there is one, is of
            // key type OptArgIndexKey::None.
            if let Some(index_loc) = skeleton.clauses[target_pos]
                .opt_arg_index_key
                .switch_on_term_loc()
            {
                let inner_clause_start = find_inner_choice_instr(
                    code,
                    skeleton.clauses[target_pos].clause_start,
                    index_loc,
                );

                remove_index_from_subsequence(
                    code,
                    &skeleton.clauses[target_pos].opt_arg_index_key,
                    inner_clause_start,
                    &mut self.payload.retraction_info,
                );

                match derelictize_try_me_else(
                    code,
                    inner_clause_start,
                    &mut self.payload.retraction_info,
                ) {
                    Some(offset) => {
                        let instr_loc =
                            find_inner_choice_instr(code, inner_clause_start + offset, index_loc);

                        let clause_loc = blunt_leading_choice_instr(
                            code,
                            instr_loc,
                            &mut self.payload.retraction_info,
                        );

                        set_switch_var_offset(
                            code,
                            index_loc,
                            clause_loc - index_loc,
                            &mut self.payload.retraction_info,
                        );

                        self.payload.retraction_info.push_record(
                            RetractionRecord::SkeletonClauseStartReplaced(
                                payload_compilation_target,
                                key,
                                target_pos + 1,
                                skeleton.clauses[target_pos + 1].clause_start,
                            ),
                        );

                        skeleton.clauses[target_pos + 1].clause_start =
                            skeleton.clauses[target_pos].clause_start;

                        let update_code_index = target_pos == 0
                            && skeleton.clauses[target_pos + 1]
                                .opt_arg_index_key
                                .switch_on_term_loc()
                                .is_none();

                        let index_ptr_opt = if update_code_index {
                            Some(IndexPtr::index(clause_loc))
                        } else {
                            None
                        };

                        return finalize_retract(
                            key,
                            payload_compilation_target,
                            skeleton,
                            code_index,
                            target_pos,
                            index_ptr_opt,
                            &mut self.payload.retraction_info,
                        );
                    }
                    None => {
                        let index_ptr_opt = if target_pos > 0 {
                            let preceding_choice_instr_loc =
                                skeleton.clauses[target_pos - 1].clause_start;

                            remove_non_leading_clause(
                                code,
                                preceding_choice_instr_loc,
                                skeleton.clauses[target_pos].clause_start - 2,
                                &mut self.payload.retraction_info,
                            )
                        } else {
                            remove_leading_unindexed_clause(
                                code,
                                skeleton.clauses[target_pos].clause_start - 2,
                                &mut self.payload.retraction_info,
                            )
                        };

                        return finalize_retract(
                            key,
                            payload_compilation_target,
                            skeleton,
                            code_index,
                            target_pos,
                            index_ptr_opt,
                            &mut self.payload.retraction_info,
                        );
                    }
                }
            }
        }

        let index_ptr_opt = match skeleton.clauses[lower_bound]
            .opt_arg_index_key
            .switch_on_term_loc()
        {
            Some(target_indexing_loc)
                if mergeable_indexed_subsequences(lower_bound, target_pos, skeleton) =>
            {
                let lower_bound_clause_start = find_inner_choice_instr(
                    code,
                    skeleton.clauses[lower_bound].clause_start,
                    target_indexing_loc,
                );

                let result;

                match skeleton.clauses[target_pos + 1]
                    .opt_arg_index_key
                    .switch_on_term_loc()
                {
                    Some(later_indexing_loc) if later_indexing_loc < target_indexing_loc => {
                        let target_indexing_line = mem::replace(
                            &mut code[target_indexing_loc],
                            Instruction::RevJmpBy(target_indexing_loc - later_indexing_loc),
                        );

                        if let Instruction::IndexingCode(indexing_code) = target_indexing_line {
                            self.payload.retraction_info.push_record(
                                RetractionRecord::ReplacedIndexingLine(
                                    target_indexing_loc,
                                    indexing_code,
                                ),
                            );
                        }

                        result = merge_indexed_subsequences(
                            code,
                            skeleton,
                            lower_bound,
                            target_pos + 1,
                            &mut self.payload.retraction_info,
                        );

                        merge_indices(
                            code,
                            later_indexing_loc,
                            0..target_pos - lower_bound,
                            &mut skeleton.clauses.make_contiguous()[lower_bound..],
                            &skeleton.core.retracted_dynamic_clauses,
                            &mut self.payload.retraction_info,
                        );

                        set_switch_var_offset(
                            code,
                            later_indexing_loc,
                            lower_bound_clause_start - later_indexing_loc,
                            &mut self.payload.retraction_info,
                        );
                    }
                    _ => {
                        result = merge_indexed_subsequences(
                            code,
                            skeleton,
                            lower_bound,
                            target_pos + 1,
                            &mut self.payload.retraction_info,
                        );

                        merge_indices(
                            code,
                            target_indexing_loc,
                            target_pos + 1 - lower_bound..skeleton.clauses.len() - lower_bound,
                            &mut skeleton.clauses.make_contiguous()[lower_bound..],
                            &skeleton.core.retracted_dynamic_clauses,
                            &mut self.payload.retraction_info,
                        );

                        set_switch_var_offset_to_choice_instr(
                            code,
                            target_indexing_loc,
                            lower_bound_clause_start - target_indexing_loc,
                            &mut self.payload.retraction_info,
                        );
                    }
                };

                result
            }
            _ => {
                if target_pos > 0 {
                    remove_index_from_subsequence(
                        code,
                        &skeleton.clauses[target_pos].opt_arg_index_key,
                        skeleton.clauses[target_pos].clause_start,
                        &mut self.payload.retraction_info,
                    );

                    match skeleton.clauses[target_pos]
                        .opt_arg_index_key
                        .switch_on_term_loc()
                    {
                        Some(index_loc) => {
                            let clause_start = find_inner_choice_instr(
                                code,
                                skeleton.clauses[target_pos].clause_start,
                                index_loc,
                            );

                            let lower_bound_clause_start =
                                skeleton.clauses[lower_bound].clause_start;
                            let preceding_choice_instr_loc;

                            match &mut code[clause_start] {
                                Instruction::TryMeElse(0) => {
                                    preceding_choice_instr_loc = if skeleton.clauses[lower_bound]
                                        .opt_arg_index_key
                                        .is_some()
                                    {
                                        lower_bound_clause_start - 2
                                    } else {
                                        lower_bound_clause_start
                                    };

                                    remove_non_leading_clause(
                                        code,
                                        preceding_choice_instr_loc,
                                        skeleton.clauses[target_pos].clause_start - 2,
                                        &mut self.payload.retraction_info,
                                    );
                                }
                                Instruction::TryMeElse(_) => {
                                    let new_target_loc = blunt_leading_choice_instr(
                                        code,
                                        clause_start,
                                        &mut self.payload.retraction_info,
                                    );

                                    derelictize_try_me_else(
                                        code,
                                        clause_start,
                                        &mut self.payload.retraction_info,
                                    );

                                    set_switch_var_offset(
                                        code,
                                        index_loc,
                                        new_target_loc - index_loc,
                                        &mut self.payload.retraction_info,
                                    );

                                    self.payload.retraction_info.push_record(
                                        RetractionRecord::SkeletonClauseStartReplaced(
                                            payload_compilation_target,
                                            key,
                                            target_pos + 1,
                                            skeleton.clauses[target_pos + 1].clause_start,
                                        ),
                                    );

                                    skeleton.clauses[target_pos + 1].clause_start =
                                        skeleton.clauses[target_pos].clause_start;
                                }
                                _ => {
                                    preceding_choice_instr_loc = find_inner_choice_instr(
                                        code,
                                        skeleton.clauses[target_pos - 1].clause_start,
                                        index_loc,
                                    );

                                    remove_non_leading_clause(
                                        code,
                                        preceding_choice_instr_loc,
                                        skeleton.clauses[target_pos].clause_start,
                                        &mut self.payload.retraction_info,
                                    );

                                    if let Instruction::TryMeElse(0) =
                                        &mut code[preceding_choice_instr_loc]
                                    {
                                        set_switch_var_offset(
                                            code,
                                            index_loc,
                                            preceding_choice_instr_loc + 1 - index_loc,
                                            &mut self.payload.retraction_info,
                                        );
                                    }
                                }
                            }

                            None
                        }
                        None => {
                            let preceding_choice_instr_loc =
                                if skeleton.clauses[lower_bound].opt_arg_index_key.is_some() {
                                    skeleton.clauses[lower_bound].clause_start - 2
                                } else {
                                    skeleton.clauses[lower_bound].clause_start
                                };

                            remove_non_leading_clause(
                                code,
                                preceding_choice_instr_loc,
                                skeleton.clauses[target_pos].clause_start,
                                &mut self.payload.retraction_info,
                            )
                        }
                    }
                } else {
                    remove_leading_unindexed_clause(
                        code,
                        skeleton.clauses[target_pos].clause_start,
                        &mut self.payload.retraction_info,
                    )
                }
            }
        };

        finalize_retract(
            key,
            payload_compilation_target,
            skeleton,
            code_index,
            target_pos,
            index_ptr_opt,
            &mut self.payload.retraction_info,
        )
    }
}

impl<'a, LS: LoadState<'a>> Loader<'a, LS> {
    pub(super) fn compile_clause_clauses<ClauseIter: Iterator<Item = (Term, Term)>>(
        &mut self,
        key: PredicateKey,
        compilation_target: CompilationTarget,
        clause_clauses: ClauseIter,
        append_or_prepend: AppendOrPrepend,
    ) -> Result<(), SessionError> {
        let clause_predicates = clause_clauses
            .map(|(head, body)| Term::Clause(Cell::default(), atom!("$clause"), vec![head, body]));

        let clause_clause_compilation_target = match compilation_target {
            CompilationTarget::User => CompilationTarget::Module(atom!("builtins")),
            _ => compilation_target,
        };

        let mut num_clause_predicates = 0;

        for clause_term in clause_predicates {
            self.incremental_compile_clause(
                (atom!("$clause"), 2),
                clause_term,
                clause_clause_compilation_target,
                false, // non_counted_bt is false.
                append_or_prepend,
            )?;

            num_clause_predicates += 1;
        }

        let locs_vec: Vec<_> = match self
            .wam_prelude
            .indices
            .get_predicate_skeleton_mut(&compilation_target, &key)
        {
            Some(skeleton) if append_or_prepend.is_append() => {
                let tail_num = skeleton.core.clause_clause_locs.len() - num_clause_predicates;
                skeleton.core.clause_clause_locs.make_contiguous()[tail_num..].to_vec()
            }
            Some(skeleton) => skeleton.core.clause_clause_locs.make_contiguous()
                [0..num_clause_predicates]
                .to_vec(),
            None => {
                unreachable!()
            }
        };

        match self
            .wam_prelude
            .indices
            .get_predicate_skeleton_mut(&clause_clause_compilation_target, &(atom!("$clause"), 2))
        {
            Some(skeleton) if append_or_prepend.is_append() => {
                for _ in 0..num_clause_predicates {
                    skeleton.core.clause_clause_locs.pop_back();
                }

                for loc in locs_vec {
                    skeleton.core.clause_clause_locs.push_back(loc);
                }
            }
            Some(skeleton) => {
                for _ in 0..num_clause_predicates {
                    skeleton.core.clause_clause_locs.pop_front();
                }

                for loc in locs_vec.into_iter().rev() {
                    skeleton.core.clause_clause_locs.push_front(loc);
                }
            }
            None if append_or_prepend.is_append() => {
                let mut skeleton = PredicateSkeleton::new();

                for loc in locs_vec {
                    skeleton.core.clause_clause_locs.push_back(loc);
                }

                self.add_extensible_predicate(
                    (atom!("$clause"), 2),
                    skeleton,
                    clause_clause_compilation_target,
                );
            }
            None => {
                let mut skeleton = PredicateSkeleton::new();

                for loc in locs_vec.into_iter().rev() {
                    skeleton.core.clause_clause_locs.push_back(loc);
                }

                self.add_extensible_predicate(
                    (atom!("$clause"), 2),
                    skeleton,
                    clause_clause_compilation_target,
                );
            }
        }

        Ok(())
    }

    pub(super) fn compile_and_submit(&mut self) -> Result<(), SessionError> {
        let key = self
            .payload
            .predicates
            .first()
            .and_then(|cl| {
                let arity = ClauseInfo::arity(cl);
                ClauseInfo::name(cl).map(|name| (name, arity))
            })
            .ok_or(SessionError::NamelessEntry)?;

        let listing_src_file_name = self.listing_src_file_name();

        // payload_compilation_target describes the compilation context,
        // e.g. compiling
        //
        // table_wrapper:tabled(get_node(A), b).
        //
        // without a module declaration means self.payload.compilation_target
        // is CompilationTarget::User while self.payload.predicates.compilation_target
        // is CompilationTarget::Module(atom!("table_wrapper")).

        let payload_compilation_target = self.payload.compilation_target;

        let mut local_predicate_info = self
            .wam_prelude
            .indices
            .get_local_predicate_skeleton(
                payload_compilation_target,
                self.payload.predicates.compilation_target,
                listing_src_file_name,
                key,
            )
            .map(|skeleton| skeleton.predicate_info())
            .unwrap_or_default();

        let mut predicate_info = self
            .wam_prelude
            .indices
            .get_predicate_skeleton(&self.payload.predicates.compilation_target, &key)
            .map(|skeleton| skeleton.predicate_info())
            .unwrap_or_default();

        let is_cross_module_clause =
            payload_compilation_target != self.payload.predicates.compilation_target;

        local_predicate_info.is_discontiguous = predicate_info.is_discontiguous;

        if local_predicate_info.must_retract_local_clauses(is_cross_module_clause) {
            self.retract_local_clauses(&key, predicate_info.is_dynamic);
        }

        let predicates_len = self.payload.predicates.len();
        let non_counted_bt = self.payload.non_counted_bt_preds.contains(&key);

        if predicate_info.compile_incrementally() {
            let predicates = self.payload.predicates.take();

            for term in predicates.predicates {
                self.incremental_compile_clause(
                    key,
                    term,
                    self.payload.predicates.compilation_target,
                    non_counted_bt,
                    AppendOrPrepend::Append,
                )?;
            }
        } else {
            if is_cross_module_clause && !local_predicate_info.is_extensible {
                if predicate_info.is_multifile {
                    println!(
                        "Warning: overwriting multifile predicate {}:{}/{} because \
                              it was not locally declared multifile.",
                        self.payload.predicates.compilation_target,
                        key.0.as_str(),
                        key.1
                    );
                }

                if let Some(skeleton) = self
                    .wam_prelude
                    .indices
                    .remove_predicate_skeleton(&self.payload.predicates.compilation_target, &key)
                {
                    let compilation_target = self.payload.predicates.compilation_target;

                    if predicate_info.is_dynamic {
                        let clause_clause_compilation_target = match compilation_target {
                            CompilationTarget::User => CompilationTarget::Module(atom!("builtins")),
                            module => module,
                        };

                        self.retract_local_clauses_by_locs(
                            clause_clause_compilation_target,
                            (atom!("$clause"), 2),
                            (0..skeleton.clauses.len()).map(Some).collect(),
                            false, // the builtin M:'$clause'/2 is never dynamic.
                        );

                        predicate_info.is_dynamic = false;
                    }

                    self.payload
                        .retraction_info
                        .push_record(RetractionRecord::RemovedSkeleton(
                            compilation_target,
                            key,
                            skeleton,
                        ));
                }
            }

            let settings = CodeGenSettings {
                global_clock_tick: if predicate_info.is_dynamic {
                    Some(LS::machine_st(&mut self.payload).global_clock)
                } else {
                    None
                },
                is_extensible: predicate_info.is_extensible,
                non_counted_bt,
            };

            let predicates = self.payload.predicates.take();
            let code_index = self.compile(key, predicates, settings)?;

            if let Some(filename) = self.listing_src_file_name() {
                if let Some(ref mut module) = self.wam_prelude.indices.modules.get_mut(&filename) {
                    let index_ptr = code_index.get();
                    let code_index = *module.code_dir.entry(key).or_insert(code_index);

                    set_code_index(
                        &mut self.payload.retraction_info,
                        &CompilationTarget::Module(filename),
                        key,
                        code_index,
                        index_ptr,
                    );
                }
            }
        }

        if predicate_info.is_dynamic {
            LS::machine_st(&mut self.payload).global_clock += 1;

            let clause_clauses_len = self.payload.clause_clauses.len();
            let clauses_vec: Vec<_> = self
                .payload
                .clause_clauses
                .drain(0..std::cmp::min(predicates_len, clause_clauses_len))
                .collect();

            let compilation_target = self.payload.predicates.compilation_target;

            self.compile_clause_clauses(
                key,
                compilation_target,
                clauses_vec.into_iter(),
                AppendOrPrepend::Append,
            )?;
        }

        Ok(())
    }
}

// standalone functions for compiling auxiliary goals used by expand_goal.
impl Machine {
    pub(crate) fn get_or_insert_qualified_code_index(
        &mut self,
        module_name: HeapCellValue,
        key: PredicateKey,
    ) -> CodeIndex {
        let mut loader: Loader<'_, InlineLoadState<'_>> = Loader::new(self, InlineTermStream {});

        let module_name = if module_name.get_tag() == HeapCellValueTag::Atom {
            cell_as_atom!(module_name)
        } else {
            atom!("user")
        };

        loader.get_or_insert_qualified_code_index(module_name, key)
    }

    pub(crate) fn compile_standalone_clause(
        &mut self,
        term_loc: RegType,
        vars: &[Term],
    ) -> Result<(), SessionError> {
        let mut compile = || {
            let mut loader: Loader<'_, InlineLoadState<'_>> =
                Loader::new(self, InlineTermStream {});

            let term = loader.read_term_from_heap(term_loc);
            let clause = build_rule_body(vars, term);

            let settings = CodeGenSettings {
                global_clock_tick: None,
                is_extensible: false,
                non_counted_bt: true,
            };

            loader.compile_standalone_clause(clause, settings)
        };

        let StandaloneCompileResult { clause_code, .. } = compile()?;
        self.code.extend(clause_code);

        Ok(())
    }
}
