use crate::codegen::*;
use crate::debray_allocator::*;
use crate::indexing::{merge_clause_index, remove_index};
use crate::machine::load_state::set_code_index;
use crate::machine::loader::*;
use crate::machine::load_state::LoadState;
use crate::machine::*;
use crate::machine::term_stream::*;

use slice_deque::sdeq;

use std::cell::Cell;
use std::collections::VecDeque;
use std::ops::Range;

struct StandaloneCompileResult {
    clause_code: Code,
    standalone_skeleton: PredicateSkeleton,
}

pub(super)
fn bootstrapping_compile(
    stream: Stream,
    wam: &mut Machine,
    listing_src: ListingSource,
) -> Result<(), SessionError> {
    let stream = &mut parsing_stream(stream)?;
    let term_stream =
        BootstrappingTermStream::from_prolog_stream(
            stream,
            wam.machine_st.atom_tbl.clone(),
            wam.machine_st.flags,
            listing_src,
        );

    let loader = Loader::new(term_stream, wam);
    loader.load()?;

    Ok(())
}

// throw errors if declaration or query found.
pub(super)
fn compile_relation(
    cg: &mut CodeGenerator<DebrayAllocator>,
    tl: &TopLevel
) -> Result<Code, CompilationError> {
    match tl {
        &TopLevel::Declaration(_) | &TopLevel::Query(_) =>
            Err(CompilationError::ExpectedRel),
        &TopLevel::Predicate(ref clauses) =>
            cg.compile_predicate(&clauses),
        &TopLevel::Fact(ref fact, ..) =>
            Ok(cg.compile_fact(fact)),
        &TopLevel::Rule(ref rule, ..) =>
            cg.compile_rule(rule),
    }
}

pub(super)
fn compile_appendix(
    code: &mut Code,
    queue: &VecDeque<TopLevel>,
    jmp_by_locs: Vec<usize>,
    non_counted_bt: bool,
    atom_tbl: TabledData<Atom>,
) -> Result<(), CompilationError> {
    let mut jmp_by_locs = VecDeque::from(jmp_by_locs);

    for tl in queue.iter() {
        let code_len = code.len();
        let jmp_by_offset = jmp_by_locs.pop_front().unwrap();

        match &mut code[jmp_by_offset] {
            &mut Line::Control(ControlInstruction::JmpBy(_, ref mut offset, ..)) => {
                *offset = code_len - jmp_by_offset;
            }
            _ => {
                unreachable!()
            }
        }

        // false because the inner predicate is a one-off, hence not extensible.
        let settings = CodeGenSettings::new(false, non_counted_bt);

        let mut cg = CodeGenerator::<DebrayAllocator>::new(atom_tbl.clone(), settings);
        let decl_code = compile_relation(&mut cg, tl)?;

        jmp_by_locs.extend(cg.jmp_by_locs.into_iter().map(|offset| offset + code.len()));
        code.extend(decl_code.into_iter());
    }

    Ok(())
}

fn lower_bound_of_target_clause(skeleton: &PredicateSkeleton, target_pos: usize) -> usize {
    if target_pos == 0 {
        return 0;
    }

    let arg_num = skeleton.clauses[target_pos - 1].opt_arg_index_key.arg_num();

    if arg_num == 0 {
        return target_pos - 1;
    }

    for index in (0 .. target_pos - 1).rev() {
        let current_arg_num = skeleton.clauses[index].opt_arg_index_key.arg_num();

        if current_arg_num == 0 || current_arg_num != arg_num {
            return index + 1;
        }
    }

    0
}

fn compile_standalone_clause(
    clause: PredicateClause,
    queue: VecDeque<TopLevel>,
    settings: CodeGenSettings,
    atom_tbl: TabledData<Atom>,
) -> Result<StandaloneCompileResult, SessionError> {
    let mut cg = CodeGenerator::<DebrayAllocator>::new(atom_tbl.clone(), settings);
    let mut clause_code = cg.compile_predicate(&vec![clause])?;

    compile_appendix(
        &mut clause_code,
        &queue,
        cg.jmp_by_locs,
        settings.non_counted_bt,
        atom_tbl,
    )?;

    Ok(StandaloneCompileResult {
        clause_code,
        standalone_skeleton: cg.skeleton,
    })
}

fn derelictize_try_me_else(
    code: &mut Code,
    index: usize,
    retraction_info: &mut RetractionInfo,
) -> Option<usize> {
    match &mut code[index] {
        Line::Choice(ChoiceInstruction::TryMeElse(0)) => {
            None
        }
        Line::Choice(ChoiceInstruction::TryMeElse(ref mut offset)) => {
            retraction_info.push_record(
                RetractionRecord::ModifiedTryMeElse(index, *offset),
            );

            Some(mem::replace(offset, 0))
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
    retraction_info: &mut RetractionInfo,
) {
    for clause_index in index_range {
        if let Some(index_loc) = skeleton[clause_index].opt_arg_index_key.switch_on_term_loc() {
            let clause_loc =
                find_inner_choice_instr(code, skeleton[clause_index].clause_start, index_loc);

            let target_indexing_line =
                to_indexing_line_mut(&mut code[target_index_loc]).unwrap();

            skeleton[clause_index].opt_arg_index_key.set_switch_on_term_loc(target_index_loc);

            merge_clause_index(
                target_indexing_line,
                &mut skeleton[0 .. clause_index + 1],
                clause_loc,
                AppendOrPrepend::Append,
            );

            retraction_info.push_record(
                RetractionRecord::AddedIndex(
                    skeleton[clause_index].opt_arg_index_key.clone(),
                    clause_loc,
                ),
            );
        } else {
            break;
        }
    }
}

fn find_inner_choice_instr(
    code: &Code,
    mut index: usize,
    index_loc: usize,
) -> usize {
    loop {
        match &code[index] {
            Line::Choice(ChoiceInstruction::TryMeElse(o)) |
            Line::Choice(ChoiceInstruction::RetryMeElse(o)) => {
                if *o > 0 {
                    return index;
                } else {
                    index = index_loc;
                }
            }
            Line::Choice(ChoiceInstruction::TrustMe(_)) => {
                return index;
            }
            Line::IndexingCode(indexing_code) => {
                match &indexing_code[0] {
                    IndexingLine::Indexing(
                        IndexingInstruction::SwitchOnTerm(_, v, ..)
                    ) => {
                        index += v;
                    }
                    _ => {
                        unreachable!();
                    }
                }
            }
            Line::Control(ControlInstruction::RevJmpBy(offset)) => {
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

        let target_indexing_line =
            to_indexing_line_mut(&mut code[index_loc]).unwrap();

        let offset = clause_start - index_loc + 1;

        remove_index(opt_arg_index_key, target_indexing_line, offset);

        // TODO: this isn't sufficiently precise. The removed offset could
        // appear anywhere inside an Internal record.
        retraction_info.push_record(
            RetractionRecord::RemovedIndex(
                index_loc,
                opt_arg_index_key.clone(),
                offset,
            ),
        );
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

    let inner_trust_me_loc =
        skeleton.clauses[upper_lower_bound - 2].clause_start;

    let inner_try_me_else_loc = find_inner_choice_instr(
        code,
        skeleton.clauses[upper_lower_bound].clause_start,
        skeleton.clauses[upper_lower_bound].opt_arg_index_key
            .switch_on_term_loc().unwrap(),
    );

    match &mut code[inner_try_me_else_loc] {
        Line::Choice(ChoiceInstruction::TryMeElse(ref mut o)) => {
            retraction_info.push_record(
                RetractionRecord::ModifiedTryMeElse(
                    skeleton.clauses[upper_lower_bound].clause_start,
                    *o,
                ),
            );

            match *o {
                0 => {
                    code[inner_try_me_else_loc] =
                        Line::Choice(ChoiceInstruction::TrustMe(0));
                }
                o => {
                    match &code[inner_try_me_else_loc + o] {
                        Line::Control(ControlInstruction::RevJmpBy(0)) => {
                            code[inner_try_me_else_loc] =
                                Line::Choice(ChoiceInstruction::TrustMe(o));
                        }
                        _ => {
                            code[inner_try_me_else_loc] =
                                Line::Choice(ChoiceInstruction::RetryMeElse(o));
                        }
                    }
                }
            }
        }
        _ => {
        }
    }

    thread_choice_instr_at_to(
        code,
        inner_trust_me_loc,
        inner_try_me_else_loc,
        retraction_info,
    );

    let mut end_of_upper_lower_bound = None;

    for index in upper_lower_bound .. skeleton.clauses.len() {
        if !skeleton.clauses[index].opt_arg_index_key.is_some() {
            end_of_upper_lower_bound = Some(index);
            break;
        }
    }

    let outer_threaded_choice_instr_loc =
        skeleton.clauses[lower_upper_bound].clause_start - 2;

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
            match &mut code[outer_threaded_choice_instr_loc] {
                Line::Choice(ChoiceInstruction::TryMeElse(ref mut o)) => {
                    retraction_info.push_record(
                        RetractionRecord::ModifiedTryMeElse(inner_trust_me_loc, *o),
                    );

                    *o = 0;

                    return Some(IndexPtr::Index(outer_threaded_choice_instr_loc + 1));
                }
                _ => {
                }
            }
        }
    }

    None
}

fn delete_from_dynamic_skeleton(
    compilation_target: CompilationTarget,
    key: PredicateKey,
    skeleton: &mut PredicateSkeleton,
    target_pos: usize,
    retraction_info: &mut RetractionInfo,
) -> usize {
    let clause_clause_loc = skeleton.clause_clause_locs.remove(target_pos);
    let clause_index_info = skeleton.clauses.remove(target_pos);

    retraction_info.push_record(
        RetractionRecord::RemovedDynamicSkeletonClause(
            compilation_target,
            key,
            target_pos,
            clause_index_info,
            clause_clause_loc,
        ),
    );

    clause_clause_loc
}

fn blunt_leading_choice_instr(
    code: &mut Code,
    mut instr_loc: usize,
    retraction_info: &mut RetractionInfo,
) -> usize {
    loop {
        match &mut code[instr_loc] {
            Line::Choice(ChoiceInstruction::RetryMeElse(o)) => {
                retraction_info.push_record(
                    RetractionRecord::ModifiedRetryMeElse(instr_loc, *o),
                );

                code[instr_loc] = Line::Choice(ChoiceInstruction::TryMeElse(*o));

                return instr_loc;
            }
            Line::Choice(ChoiceInstruction::TrustMe(offset)) => {
                retraction_info.push_record(
                    RetractionRecord::AppendedTrustMe(instr_loc, *offset, false),
                );

                code[instr_loc] = Line::Choice(ChoiceInstruction::TryMeElse(0));
                return instr_loc + 1;
            }
            Line::Choice(ChoiceInstruction::TryMeElse(0)) => {
                return instr_loc + 1;
            }
            Line::Choice(ChoiceInstruction::TryMeElse(o)) => {
                instr_loc += *o;
            }
            Line::Control(ControlInstruction::RevJmpBy(o)) => {
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
    let target_indexing_line =
        to_indexing_line_mut(&mut code[index_loc]).unwrap();

    let v =
        match &mut target_indexing_line[0] {
            IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(_, v, ..)) => {
                *v
            }
            _ => {
                unreachable!();
            }
        };

    match &code[index_loc + v] {
        Line::Choice(ChoiceInstruction::TryMeElse(_)) => {
        }
        _ => {
            set_switch_var_offset(
                code,
                index_loc,
                offset,
                retraction_info,
            );
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
    let target_indexing_line =
        to_indexing_line_mut(&mut code[index_loc]).unwrap();

    let old_v =
        match &mut target_indexing_line[0] {
            IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(_, ref mut v, ..)) => {
                mem::replace(v, offset)
            }
            _ => {
                unreachable!()
            }
        };

    retraction_info.push_record(
        RetractionRecord::ReplacedSwitchOnTermVarIndex(index_loc, old_v),
    );
}

fn internalize_choice_instr_at(
    code: &mut Code,
    instr_loc: usize,
    retraction_info: &mut RetractionInfo,
) {
    match &mut code[instr_loc] {
        Line::Choice(ChoiceInstruction::TryMeElse(0)) => {
            retraction_info.push_record(
                RetractionRecord::ModifiedTryMeElse(instr_loc, 0),
            );

            code[instr_loc] = Line::Choice(ChoiceInstruction::TrustMe(0));
        }
        Line::Choice(ChoiceInstruction::TryMeElse(o)) => {
            let o = *o;

            retraction_info.push_record(
                RetractionRecord::ModifiedTryMeElse(instr_loc, o),
            );

            match &mut code[instr_loc + o] {
                Line::Control(ControlInstruction::RevJmpBy(p))
                    if *p == 0 => {
                        code[instr_loc] = Line::Choice(ChoiceInstruction::TrustMe(o));
                    }
                _ => {
                    code[instr_loc] = Line::Choice(ChoiceInstruction::RetryMeElse(o));
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
            Line::Choice(ChoiceInstruction::TryMeElse(ref mut o)) |
            Line::Choice(ChoiceInstruction::RetryMeElse(ref mut o))
                if target_loc >= instr_loc => {
                    retraction_info.push_record(
                        RetractionRecord::ReplacedChoiceOffset(instr_loc, *o),
                    );

                    *o = target_loc - instr_loc;
                    return;
                }
            Line::Choice(ChoiceInstruction::TryMeElse(ref mut o)) |
            Line::Choice(ChoiceInstruction::RetryMeElse(ref mut o)) => {
                instr_loc += *o;
            }
            Line::Control(ControlInstruction::RevJmpBy(ref mut o))
                if instr_loc >= target_loc => {
                    retraction_info.push_record(
                        RetractionRecord::ModifiedRevJmpBy(instr_loc, *o),
                    );

                    *o = instr_loc - target_loc;
                    return;
                }
            Line::Choice(ChoiceInstruction::TrustMe(ref mut o))
                if target_loc >= instr_loc => {
                    retraction_info.push_record(
                        RetractionRecord::AppendedTrustMe(instr_loc, *o, false),
                        //choice_instr.is_default()),
                    );

                    code[instr_loc] =
                        Line::Choice(ChoiceInstruction::RetryMeElse(target_loc - instr_loc));

                    return;
                }
            Line::Choice(ChoiceInstruction::TrustMe(o))
                if *o > 0 => {
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
        Line::Choice(ChoiceInstruction::RetryMeElse(ref mut o)) => {
            let o = *o;

            thread_choice_instr_at_to(
                code,
                preceding_choice_instr_loc,
                non_indexed_choice_instr_loc + o,
                retraction_info,
            );

            None
        }
        Line::Choice(ChoiceInstruction::TrustMe(_)) => {
            match &mut code[preceding_choice_instr_loc] {
                Line::Choice(ChoiceInstruction::RetryMeElse(o)) => {
                    retraction_info.push_record(
                        RetractionRecord::ModifiedRetryMeElse(
                            preceding_choice_instr_loc,
                            *o,
                        ),
                    );

                    code[preceding_choice_instr_loc] =
                        Line::Choice(ChoiceInstruction::TrustMe(0));

                    None
                }
                Line::Choice(ChoiceInstruction::TryMeElse(ref mut o)) => {
                    retraction_info.push_record(
                        RetractionRecord::ModifiedTryMeElse(
                            preceding_choice_instr_loc,
                            *o,
                        )
                    );

                    *o = 0;

                    Some(IndexPtr::Index(preceding_choice_instr_loc + 1))
                }
                _ => {
                    unreachable!();
                }
            }
        }
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
    let clause_clause_loc =
        delete_from_dynamic_skeleton(
            compilation_target.clone(),
            key.clone(),
            skeleton,
            target_pos,
            retraction_info,
        );

    if let Some(index_ptr) = index_ptr_opt {
        set_code_index(
            retraction_info,
            &compilation_target,
            key,
            &code_index,
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
        Line::Choice(ChoiceInstruction::TryMeElse(ref mut o)) => {
            if *o > 0 {
                retraction_info.push_record(
                    RetractionRecord::ModifiedTryMeElse(
                        non_indexed_choice_instr_loc,
                        *o,
                    )
                );

                let o = mem::replace(o, 0);

                let index_ptr = blunt_leading_choice_instr(
                    code,
                    non_indexed_choice_instr_loc + o,
                    retraction_info,
                );

                Some(IndexPtr::Index(index_ptr))
            } else {
                Some(IndexPtr::DynamicUndefined)
            }
        }
        _ => {
            unreachable!();
        }
    }
}

fn prepend_compiled_clause(
    code: &mut Code,
    compilation_target: CompilationTarget,
    key: PredicateKey,
    mut clause_code: Code,
    skeleton: &mut PredicateSkeleton,
    retraction_info: &mut RetractionInfo,
) -> usize {
    let clause_loc = code.len();
    let mut prepend_queue = sdeq![];

    let target_arg_num = skeleton.clauses[0].opt_arg_index_key.arg_num();
    let head_arg_num = skeleton.clauses[1].opt_arg_index_key.arg_num();

    if skeleton.clauses[0].opt_arg_index_key.switch_on_term_loc().is_some() {
        match skeleton.clauses[1].opt_arg_index_key.switch_on_term_loc() {
            Some(index_loc) if target_arg_num == head_arg_num => {
                prepend_queue.extend(clause_code.drain(3 ..));

                skeleton.clauses[0].opt_arg_index_key += index_loc - 1;
                skeleton.clauses[0].clause_start = clause_loc + 2;

                retraction_info.push_record(
                    RetractionRecord::AddedIndex(
                        skeleton.clauses[0].opt_arg_index_key.clone(),
                        skeleton.clauses[0].clause_start,
                    ),
                );

                let outer_thread_choice_loc = skeleton.clauses[1].clause_start - 2;

                retraction_info.push_record(
                    RetractionRecord::SkeletonClauseStartReplaced(
                        compilation_target,
                        key.clone(),
                        1,
                        skeleton.clauses[1].clause_start,
                    ),
                );

                skeleton.clauses[1].clause_start =
                    find_inner_choice_instr(
                        code,
                        skeleton.clauses[1].clause_start,
                        index_loc,
                    );

                let inner_thread_rev_offset =
                    3 + prepend_queue.len() + clause_loc - skeleton.clauses[1].clause_start;

                prepend_queue.push_back(
                    Line::Control(ControlInstruction::RevJmpBy(inner_thread_rev_offset)),
                );

                prepend_queue.push_front(
                    Line::Choice(ChoiceInstruction::TryMeElse(prepend_queue.len())),
                );

                // prepend_queue is now:
                //      | TryMeElse N_2
                //      | (clause_code)
                // +N_2 | RevJmpBy (RetryMeElse(M_1) or TryMeElse(0) at index_loc + 1)

                prepend_queue.push_front(
                    Line::Control(ControlInstruction::RevJmpBy(
                        1 + clause_loc - index_loc
                    )),
                );

                let outer_thread_choice_offset = // outer_thread_choice_loc WAS index_loc - 1..
                    match derelictize_try_me_else(code, outer_thread_choice_loc, retraction_info) {
                        Some(next_subseq_offset) => {
                            // skeleton.clauses[1] has a non-stub TryMeElse.

                            let outer_thread_rev_offset =
                                prepend_queue.len() + 1 + clause_loc - outer_thread_choice_loc -
                                next_subseq_offset;

                            prepend_queue.push_back(
                                Line::Control(ControlInstruction::RevJmpBy(outer_thread_rev_offset))
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

                            prepend_queue.push_back(
                                Line::Control(ControlInstruction::RevJmpBy(0)),
                            );

                            0
                        }
                    };

                prepend_queue.push_front(
                    Line::Choice(ChoiceInstruction::TryMeElse(outer_thread_choice_offset)),
                );

                // prepend_queue is now:
                //     | TryMeElse N_3
                //     | RevJmpBy (SwitchOnTerm at index_loc)
                //     | TryMeElse N_2
                //     | (clause_code)
                // N_2 | RevJmpBy (RetryMeElse(M_1) or TryMeElse(0) at index_loc + 1)
                // N_3 | RevJmpBy (TryMeElse(N_1) at index_loc - 1 or TrustMe if N_1 == 0)

                let target_indexing_line = to_indexing_line_mut(&mut code[index_loc]).unwrap();

                merge_clause_index(
                    target_indexing_line,
                    &mut skeleton.clauses,
                    clause_loc + 2, // == skeleton.clauses[0].clause_start
                    AppendOrPrepend::Prepend,
                );

                set_switch_var_offset(
                    code,
                    index_loc,
                    clause_loc - index_loc + 2,
                    retraction_info,
                );

                internalize_choice_instr_at(code, skeleton.clauses[1].clause_start, retraction_info);

                code.extend(prepend_queue.into_iter());

                clause_loc + (outer_thread_choice_offset == 0) as usize
            }
            _ => {
                prepend_queue.extend(clause_code.drain(1 ..));

                skeleton.clauses[0].opt_arg_index_key += clause_loc;
                skeleton.clauses[0].clause_start = clause_loc + 2;

                let old_clause_start = skeleton.clauses[1].clause_start;

                let inner_thread_rev_offset =
                    2 + prepend_queue.len() + clause_loc - old_clause_start;

                // this is a stub for chaining inner-threaded choice
                // instructions.
                prepend_queue.push_back(
                    Line::Control(ControlInstruction::RevJmpBy(0))
                );

                let prepend_queue_len = prepend_queue.len();

                match &mut prepend_queue[1] {
                    Line::Choice(ChoiceInstruction::TryMeElse(ref mut o))
                        if *o == 0 => {
                            *o = prepend_queue_len - 2;
                        }
                    _ => {
                        unreachable!();
                    }
                }

                prepend_queue.push_back(
                    Line::Control(ControlInstruction::RevJmpBy(inner_thread_rev_offset)),
                );

                prepend_queue.push_front(
                    Line::Choice(ChoiceInstruction::TryMeElse(prepend_queue.len())),
                );

                // prepend_queue is now:
                //      | TryMeElse(N_2)
                //      | SwitchOnTerm 2, ...
                //      | TryMeElse(0)
                //      | (clause_code)
                // +N_2 | RevJmpBy (RetryMeElse(M_1))

                internalize_choice_instr_at(code, old_clause_start, retraction_info);

                code.extend(prepend_queue.into_iter());

                clause_loc // + (outer_thread_choice_offset == 0 as usize)
            }
        }
    } else {
        match skeleton.clauses[1].opt_arg_index_key.switch_on_term_loc() {
            Some(_) => {
                prepend_queue.extend(clause_code.drain(1 ..));

                let old_clause_start = skeleton.clauses[1].clause_start - 2;

                let inner_thread_rev_offset =
                    1 + prepend_queue.len() + clause_loc - old_clause_start;

                prepend_queue.push_back(
                    Line::Control(ControlInstruction::RevJmpBy(inner_thread_rev_offset)),
                );

                prepend_queue.push_front(
                    Line::Choice(ChoiceInstruction::TryMeElse(prepend_queue.len())),
                );

                // prepend_queue is now:
                //      | TryMeElse(N_2)
                //      | (clause_code)
                // +N_2 | RevJmpBy (RetryMeElse(M_1))

                internalize_choice_instr_at(code, old_clause_start, retraction_info);

                code.extend(prepend_queue.into_iter());

                // skeleton.clauses[0].opt_arg_index_key += clause_loc;
                skeleton.clauses[0].clause_start = clause_loc;

                clause_loc // + (outer_thread_choice_offset == 0 as usize)
            }
            None => {
                prepend_queue.extend(clause_code.drain(1 ..));

                let old_clause_start = skeleton.clauses[1].clause_start;

                let inner_thread_rev_offset =
                    1 + prepend_queue.len() + clause_loc - old_clause_start;

                prepend_queue.push_back(
                    Line::Control(ControlInstruction::RevJmpBy(inner_thread_rev_offset)),
                );

                prepend_queue.push_front(
                    Line::Choice(ChoiceInstruction::TryMeElse(prepend_queue.len())),
                );

                // prepend_queue is now:
                //      | TryMeElse(N_2)
                //      | (clause_code)
                // +N_2 | RevJmpBy (RetryMeElse(M_1))

                internalize_choice_instr_at(code, old_clause_start, retraction_info);

                code.extend(prepend_queue.into_iter());

                // skeleton.clauses[0].opt_arg_index_key += clause_loc;
                skeleton.clauses[0].clause_start = clause_loc;

                clause_loc // + (outer_thread_choice_offset == 0 as usize)
            }
        }
    }
}

fn append_compiled_clause(
    code: &mut Code,
    mut clause_code: Code,
    skeleton: &mut PredicateSkeleton,
    retraction_info: &mut RetractionInfo,
) -> Option<usize> {
    let clause_loc = code.len();
    let target_pos = skeleton.clauses.len() - 1;
    let lower_bound = lower_bound_of_target_clause(skeleton, target_pos);

    code.push(Line::Choice(ChoiceInstruction::TrustMe(0)));
    skeleton.clauses[target_pos].clause_start = clause_loc;

    let mut code_ptr_opt = None;

    let lower_bound_arg_num = skeleton.clauses[lower_bound].opt_arg_index_key.arg_num();
    let target_arg_num = skeleton.clauses[target_pos].opt_arg_index_key.arg_num();

    let threaded_choice_instr_loc =
        match skeleton.clauses[lower_bound].opt_arg_index_key.switch_on_term_loc() {
            Some(index_loc) if lower_bound_arg_num == target_arg_num => {
                code.extend(clause_code.drain(3 ..)); // skip the indexing code

                // set skeleton[target_pos].opt_arg_index_key to
                // index_loc. its original value is always 1.
                skeleton.clauses[target_pos].opt_arg_index_key += index_loc - 1;

                retraction_info.push_record(
                    RetractionRecord::AddedIndex(
                        skeleton.clauses[target_pos].opt_arg_index_key.clone(),
                        skeleton.clauses[target_pos].clause_start,
                    ),
                );

                let target_indexing_line = to_indexing_line_mut(&mut code[index_loc]).unwrap();

                merge_clause_index(
                    target_indexing_line,
                    &mut skeleton.clauses[lower_bound ..],
                    clause_loc,
                    AppendOrPrepend::Append,
                );

                if lower_bound + 1 == target_pos {
                    let lower_bound_clause_start = find_inner_choice_instr(
                        code,
                        skeleton.clauses[lower_bound].clause_start,
                        index_loc,
                    );

                    set_switch_var_offset(
                        code,
                        index_loc,
                        lower_bound_clause_start - index_loc,
                        retraction_info,
                    );
                }

                skeleton.clauses[target_pos - 1].clause_start
            }
            _ => {
                skeleton.clauses[target_pos].opt_arg_index_key += clause_loc;
                code.extend(clause_code.drain(1 ..));

                match skeleton.clauses[lower_bound].opt_arg_index_key.switch_on_term_loc() {
                    Some(_) => {
                        if lower_bound == 0 {
                            code_ptr_opt = Some(skeleton.clauses[lower_bound].clause_start - 2);
                        }

                        skeleton.clauses[lower_bound].clause_start - 2
                    }
                    None => {
                        if lower_bound == 0 {
                            code_ptr_opt = Some(skeleton.clauses[lower_bound].clause_start);
                        }

                        match skeleton.clauses[target_pos].opt_arg_index_key.switch_on_term_loc() {
                            Some(index_loc) => {
                                // point to the inner-threaded TryMeElse(0) if target_pos is
                                // indexed, and make switch_on_term point one line after it in
                                // its variable offset.
                                skeleton.clauses[target_pos].clause_start += 2;

                                set_switch_var_offset(
                                    code,
                                    index_loc,
                                    2,
                                    retraction_info,
                                );
                            }
                            None => {
                            }
                        }

                        skeleton.clauses[lower_bound].clause_start
                    }
                }
            }
        };

    thread_choice_instr_at_to(code, threaded_choice_instr_loc, clause_loc, retraction_info);

    code_ptr_opt
}

#[inline]
fn mergeable_indexed_subsequences(
    lower_bound: usize,
    target_pos: usize,
    skeleton: &PredicateSkeleton,
) -> bool {
    let lower_bound_arg_num = skeleton.clauses[lower_bound].opt_arg_index_key.arg_num();

    if target_pos + 1 < skeleton.clauses.len() {
        let succ_arg_num   = skeleton.clauses[target_pos + 1].opt_arg_index_key.arg_num();
        let target_arg_num = skeleton.clauses[target_pos].opt_arg_index_key.arg_num();

        return target_arg_num != succ_arg_num && lower_bound_arg_num == succ_arg_num;
    }

    false
}

impl<'a> LoadState<'a> {
    fn compile(
        &mut self,
        key: PredicateKey,
        predicates: &Vec<PredicateClause>,
        queue: &VecDeque<TopLevel>,
        settings: CodeGenSettings,
    ) -> Result<IndexPtr, SessionError> {
        let code_index = self.get_or_insert_code_index(key.clone());
        let code_len = self.wam.code_repo.code.len();
        let mut code_ptr = code_len;

        let mut cg = CodeGenerator::<DebrayAllocator>::new(
            self.wam.machine_st.atom_tbl.clone(),
            settings,
        );

        let mut code = cg.compile_predicate(predicates)?;

        compile_appendix(
            &mut code,
            queue,
            cg.jmp_by_locs,
            settings.non_counted_bt,
            self.wam.machine_st.atom_tbl.clone(),
        )?;

        if settings.is_extensible {
            for clause_index_info in cg.skeleton.clauses.iter_mut() {
                clause_index_info.clause_start += code_len;
                clause_index_info.opt_arg_index_key += code_len;
            }

            match &mut code[0] {
                Line::Choice(ChoiceInstruction::TryMeElse(0)) => {
                    code_ptr += 1;
                }
                _ => {
                }
            }

            match self.wam.indices.get_predicate_skeleton(
                &self.compilation_target,
                &key,
            ) {
                Some(skeleton) => {
                    self.retraction_info.push_record(
                        RetractionRecord::SkeletonClauseTruncateBack(
                            self.compilation_target.clone(),
                            key.clone(),
                            skeleton.clauses.len(),
                        ),
                    );

                    skeleton.clauses.extend(cg.skeleton.clauses.into_iter());
                }
                None => {
                    self.add_extensible_predicate(key.clone(), cg.skeleton);
                }
            }
        }

        set_code_index(
            &mut self.retraction_info,
            &self.compilation_target,
            key,
            &code_index,
            IndexPtr::Index(code_ptr),
        );

        self.wam.code_repo.code.extend(code.into_iter());
        Ok(code_index.get())
    }

    fn record_incremental_compile(&mut self, key: PredicateKey, append_or_prepend: AppendOrPrepend)
    {
        self.retraction_info.push_record(
            match &self.compilation_target {
                CompilationTarget::User => {
                    match append_or_prepend {
                        AppendOrPrepend::Append => {
                            RetractionRecord::AppendedUserExtensiblePredicate(
                                key,
                            )
                        }
                        AppendOrPrepend::Prepend => {
                            RetractionRecord::PrependedUserExtensiblePredicate(
                                key,
                            )
                        }
                    }
                }
                CompilationTarget::Module(ref module_name) => {
                    match append_or_prepend {
                        AppendOrPrepend::Append => {
                            RetractionRecord::AppendedModuleExtensiblePredicate(
                                module_name.clone(), key,
                            )
                        }
                        AppendOrPrepend::Prepend => {
                            RetractionRecord::PrependedModuleExtensiblePredicate(
                                module_name.clone(), key,
                            )
                        }
                    }
                }
            }
        );
    }

    pub(super)
    fn incremental_compile_clause(
        &mut self,
        key: PredicateKey,
        clause: PredicateClause,
        queue: VecDeque<TopLevel>,
        non_counted_bt: bool,
        append_or_prepend: AppendOrPrepend,
    ) -> Result<IndexPtr, SessionError> {
        self.record_incremental_compile(key.clone(), append_or_prepend);

        let skeleton =
            match self.wam.indices.get_predicate_skeleton(
                &self.compilation_target,
                &key,
            ) {
                Some(skeleton) if !skeleton.clauses.is_empty() => {
                    skeleton
                }
                _ => {
                    // true because this predicate is extensible.
                    let settings = CodeGenSettings::new(true, non_counted_bt);
                    return self.compile(key, &vec![clause], &queue, settings);
                }
            };

        let settings = CodeGenSettings::new(true, non_counted_bt);
        let atom_tbl = self.wam.machine_st.atom_tbl.clone();

        let StandaloneCompileResult { clause_code, mut standalone_skeleton } =
            compile_standalone_clause(clause, queue, settings, atom_tbl)?;

        match append_or_prepend {
            AppendOrPrepend::Append => {
                skeleton.clauses.push_back(standalone_skeleton.clauses.pop_back().unwrap());

                self.retraction_info.push_record(
                    RetractionRecord::SkeletonClausePopBack(
                        self.compilation_target.clone(),
                        key.clone(),
                    ),
                );

                let result =
                    append_compiled_clause(
                        &mut self.wam.code_repo.code,
                        clause_code,
                        skeleton,
                        &mut self.retraction_info,
                    );

                let code_index = self.get_or_insert_code_index(key.clone());

                if let Some(new_code_index) = result {
                    set_code_index(
                        &mut self.retraction_info,
                        &self.compilation_target,
                        key,
                        &code_index,
                        IndexPtr::Index(new_code_index),
                    );
                }

                Ok(code_index.get())
            }
            AppendOrPrepend::Prepend => {
                skeleton.clauses.push_front(standalone_skeleton.clauses.pop_back().unwrap());

                self.retraction_info.push_record(
                    RetractionRecord::SkeletonClausePopFront(
                        self.compilation_target.clone(),
                        key.clone(),
                    ),
                );

                let threaded_choice_instr_loc =
                    prepend_compiled_clause(
                        &mut self.wam.code_repo.code,
                        self.compilation_target.clone(),
                        key.clone(),
                        clause_code,
                        skeleton,
                        &mut self.retraction_info,
                    );

                let code_index = self.get_or_insert_code_index(key.clone());

                set_code_index(
                    &mut self.retraction_info,
                    &self.compilation_target,
                    key,
                    &code_index,
                    IndexPtr::Index(threaded_choice_instr_loc),
                );

                Ok(IndexPtr::Index(threaded_choice_instr_loc))
            }
        }
    }

    pub(super)
    fn retract_clause(&mut self, key: PredicateKey, target_pos: usize) -> usize {
        let code_index = self.get_or_insert_code_index(key.clone());

        let skeleton =
            match self.wam.indices.get_predicate_skeleton(
                &self.compilation_target,
                &key,
            ) {
                Some(skeleton) => {
                    skeleton
                }
                None => {
                    unreachable!();
                }
            };

        let code = &mut self.wam.code_repo.code;
        let lower_bound = lower_bound_of_target_clause(skeleton, target_pos);
        let lower_bound_is_unindexed = !skeleton.clauses[lower_bound].opt_arg_index_key.is_some();

        if target_pos == 0 || (lower_bound + 1 == target_pos && lower_bound_is_unindexed) {
            // the clause preceding target_pos, if there is one, is of key type
            // OptArgIndexKey::None.
            match skeleton.clauses[target_pos].opt_arg_index_key.switch_on_term_loc() {
                Some(index_loc) => {
                    let inner_clause_start = find_inner_choice_instr(
                        code,
                        skeleton.clauses[target_pos].clause_start,
                        index_loc,
                    );

                    remove_index_from_subsequence(
                        code,
                        &skeleton.clauses[target_pos].opt_arg_index_key,
                        inner_clause_start,
                        &mut self.retraction_info,
                    );

                    match derelictize_try_me_else(
                        code,
                        inner_clause_start,
                        &mut self.retraction_info,
                    ) {
                        Some(offset) => {
                            let instr_loc = find_inner_choice_instr(
                                code,
                                inner_clause_start + offset,
                                index_loc,
                            );

                            let clause_loc = blunt_leading_choice_instr(
                                code,
                                instr_loc,
                                &mut self.retraction_info,
                            );

                            set_switch_var_offset(
                                code,
                                index_loc,
                                clause_loc - index_loc,
                                &mut self.retraction_info,
                            );

                            self.retraction_info.push_record(
                                RetractionRecord::SkeletonClauseStartReplaced(
                                    self.compilation_target.clone(),
                                    key.clone(),
                                    target_pos + 1,
                                    skeleton.clauses[target_pos + 1].clause_start,
                                ),
                            );

                            skeleton.clauses[target_pos + 1].clause_start =
                                skeleton.clauses[target_pos].clause_start;

                            return delete_from_dynamic_skeleton(
                                self.compilation_target.clone(),
                                key,
                                skeleton,
                                target_pos,
                                &mut self.retraction_info,
                            );
                        }
                        None => {
                            let index_ptr_opt =
                                if target_pos > 0 {
                                    let preceding_choice_instr_loc =
                                        skeleton.clauses[target_pos - 1].clause_start;

                                    remove_non_leading_clause(
                                        code,
                                        preceding_choice_instr_loc,
                                        skeleton.clauses[target_pos].clause_start - 2,
                                        &mut self.retraction_info,
                                    )
                                } else {
                                    remove_leading_unindexed_clause(
                                        code,
                                        skeleton.clauses[target_pos].clause_start - 2,
                                        &mut self.retraction_info,
                                    )
                                };

                            return finalize_retract(
                                key,
                                self.compilation_target.clone(),
                                skeleton,
                                code_index,
                                target_pos,
                                index_ptr_opt,
                                &mut self.retraction_info,
                            );
                        }
                    }
                }
                None => {
                }
            }
        }

        let index_ptr_opt =
            match skeleton.clauses[lower_bound].opt_arg_index_key.switch_on_term_loc() {
                Some(target_indexing_loc)
                    if mergeable_indexed_subsequences(lower_bound, target_pos, skeleton) =>
                {
                    let lower_bound_clause_start = find_inner_choice_instr(
                        code,
                        skeleton.clauses[lower_bound].clause_start,
                        target_indexing_loc,
                    );

                    let result;

                    match skeleton.clauses[target_pos + 1].opt_arg_index_key.switch_on_term_loc() {
                        Some(later_indexing_loc) if later_indexing_loc < target_indexing_loc => {
                            let target_indexing_line = mem::replace(
                                &mut code[target_indexing_loc],
                                Line::Control(ControlInstruction::RevJmpBy(
                                    target_indexing_loc - later_indexing_loc
                                )),
                            );

                            match target_indexing_line {
                                Line::IndexingCode(indexing_code) => {
                                    self.retraction_info.push_record(
                                        RetractionRecord::ReplacedIndexingLine(
                                            target_indexing_loc,
                                            indexing_code,
                                        ),
                                    );
                                }
                                _ => {
                                }
                            }

                            set_switch_var_offset(
                                code,
                                later_indexing_loc,
                                lower_bound_clause_start - later_indexing_loc,
                                &mut self.retraction_info,
                            );

                            result = merge_indexed_subsequences(
                                code,
                                skeleton,
                                lower_bound,
                                target_pos + 1,
                                &mut self.retraction_info,
                            );

                            merge_indices(
                                code,
                                later_indexing_loc,
                                0 .. target_pos - lower_bound,
                                &mut skeleton.clauses[lower_bound ..],
                                &mut self.retraction_info,
                            );
                        }
                        _ => {
                            set_switch_var_offset_to_choice_instr(
                                code,
                                target_indexing_loc,
                                lower_bound_clause_start - target_indexing_loc,
                                &mut self.retraction_info,
                            );

                            result = merge_indexed_subsequences(
                                code,
                                skeleton,
                                lower_bound,
                                target_pos + 1,
                                &mut self.retraction_info,
                            );

                            merge_indices(
                                code,
                                target_indexing_loc,
                                target_pos + 1 - lower_bound .. skeleton.clauses.len() - lower_bound,
                                &mut skeleton.clauses[lower_bound ..],
                                &mut self.retraction_info,
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
                            &mut self.retraction_info,
                        );

                        match skeleton.clauses[target_pos].opt_arg_index_key.switch_on_term_loc() {
                            Some(index_loc) => {
                                let preceding_choice_instr_loc = find_inner_choice_instr(
                                    code,
                                    skeleton.clauses[target_pos - 1].clause_start,
                                    index_loc,
                                );

                                remove_non_leading_clause(
                                    code,
                                    preceding_choice_instr_loc,
                                    skeleton.clauses[target_pos].clause_start,
                                    &mut self.retraction_info,
                                );

                                match &mut code[preceding_choice_instr_loc] {
                                    Line::Choice(ChoiceInstruction::TryMeElse(0)) => {
                                        set_switch_var_offset(
                                            code,
                                            index_loc,
                                            preceding_choice_instr_loc + 1 - index_loc,
                                            &mut self.retraction_info,
                                        );
                                    }
                                    _ => {
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
                                    &mut self.retraction_info,
                                )
                            }
                        }
                    } else {
                        remove_leading_unindexed_clause(
                            code,
                            skeleton.clauses[target_pos].clause_start,
                            &mut self.retraction_info,
                        )
                    }
                }
            };

        finalize_retract(
            key,
            self.compilation_target.clone(),
            skeleton,
            code_index,
            target_pos,
            index_ptr_opt,
            &mut self.retraction_info,
        )
    }
}

impl<'a, TS: TermStream> Loader<'a, TS> {
    pub(super)
    fn compile_clause_clauses<ClauseIter: Iterator<Item=(Term, Term)>>(
        &mut self,
        key: PredicateKey,
        clause_clauses: ClauseIter,
        append_or_prepend: AppendOrPrepend,
    ) -> Result<(), SessionError> {
        let clause_predicates =
            clause_clauses.map(|(head, body)| {
                PredicateClause::Fact(
                    Term::Clause(
                        Cell::default(),
                        clause_name!("$clause"),
                        vec![Box::new(head), Box::new(body)],
                        None,
                    )
                )
            });

        let compilation_target = mem::replace(
            &mut self.load_state.compilation_target,
            CompilationTarget::Module(clause_name!("builtins")),
        );

        let mut clause_clause_locs = sdeq![];

        for clause_predicate in clause_predicates {
            clause_clause_locs.push_back(self.load_state.wam.code_repo.code.len());

            let result = self.load_state.incremental_compile_clause(
                (clause_name!("$clause"), 2),
                clause_predicate,
                VecDeque::new(),
                false, // non_counted_bt is false.
                append_or_prepend,
            );

            if let Err(e) = result {
                self.load_state.compilation_target = compilation_target;
                return Err(e);
            }
        }

        match self.load_state.wam.indices.get_predicate_skeleton(
            &self.load_state.compilation_target,
            &(clause_name!("$clause"), 2),
        ) {
            Some(skeleton) if append_or_prepend.is_append() => {
                skeleton.clause_clause_locs.extend_from_slice(&clause_clause_locs[0 ..]);
            }
            Some(skeleton) => {
                for loc in clause_clause_locs.iter() {
                    skeleton.clause_clause_locs.push_front(*loc);
                }
            }
            None => {
                unreachable!();
            }
        }

        match self.load_state.wam.indices.get_predicate_skeleton(
            &compilation_target,
            &key,
        ) {
            Some(skeleton) if append_or_prepend.is_append() => {
                self.load_state.retraction_info.push_record(
                    RetractionRecord::SkeletonClauseClausesTruncateBack(
                        compilation_target.clone(),
                        key.clone(),
                        skeleton.clause_clause_locs.len(),
                    ),
                );

                skeleton.clause_clause_locs.append(
                    &mut clause_clause_locs
                );
            }
            Some(skeleton) => {
                self.load_state.retraction_info.push_record(
                    RetractionRecord::SkeletonClauseClausesTruncateFront(
                        compilation_target.clone(),
                        key.clone(),
                        skeleton.clause_clause_locs.len(),
                    ),
                );

                for loc in clause_clause_locs.iter() {
                    skeleton.clause_clause_locs.push_front(*loc);
                }

                self.load_state.increment_clause_assert_margin(
                    clause_clause_locs.len()
                );
            }
            None => {
                unreachable!();
            }
        }

        self.load_state.compilation_target = compilation_target;
        Ok(())
    }

    pub(super)
    fn compile_and_submit(&mut self) -> Result<(), SessionError> {
        let queue = self.preprocessor.parse_queue(&mut self.load_state)?;

        let key = self.predicates
            .first()
            .and_then(|cl| {
                let arity = cl.arity();
                cl.name().map(|name| (name, arity))
            })
            .ok_or(SessionError::NamelessEntry)?;

        let (is_dynamic, is_extensible) = self.load_state.wam.indices
            .get_predicate_skeleton(&self.load_state.compilation_target, &key)
            .map(|skeleton| (skeleton.is_dynamic, true))
            .unwrap_or((false, false));

        let non_counted_bt = self.non_counted_bt_preds.contains(&key);
        let settings = CodeGenSettings::new(is_extensible, non_counted_bt);

        self.load_state.compile(key.clone(), &self.predicates, &queue, settings)?;

        if is_dynamic {
            let iter = mem::replace(&mut self.clause_clauses, vec![]).into_iter();
            self.compile_clause_clauses(key, iter, AppendOrPrepend::Append)?;
        }

        Ok(self.predicates.clear())
    }
}
