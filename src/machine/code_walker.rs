use crate::instructions::*;

use indexmap::IndexSet;

fn capture_offset(line: &Line, index: usize, stack: &mut Vec<usize>) -> bool {
    match line {
        &Line::Choice(ChoiceInstruction::TryMeElse(offset)) if offset > 0 => {
            stack.push(index + offset);
        }
        &Line::Choice(ChoiceInstruction::DefaultRetryMeElse(offset))
        | &Line::Choice(ChoiceInstruction::RetryMeElse(offset))
            if offset > 0 =>
        {
            stack.push(index + offset);
        }
        &Line::Choice(ChoiceInstruction::DynamicElse(_, _, NextOrFail::Next(offset)))
            if offset > 0 =>
        {
            stack.push(index + offset);
        }
        &Line::Choice(ChoiceInstruction::DynamicInternalElse(_, _, NextOrFail::Next(offset)))
            if offset > 0 =>
        {
            stack.push(index + offset);
        }
        &Line::Control(ControlInstruction::JmpBy(_, offset, _, false)) => {
            stack.push(index + offset);
        }
        &Line::Control(ControlInstruction::JmpBy(_, offset, _, true)) => {
            stack.push(index + offset);
            return true;
        }
        &Line::Control(ControlInstruction::Proceed)
        | &Line::Control(ControlInstruction::CallClause(_, _, _, true, _)) => {
            return true;
        }
        &Line::Control(ControlInstruction::RevJmpBy(offset)) => {
            if offset > 0 {
                stack.push(index - offset);
            } else {
                return true;
            }
        }
        _ => {}
    };

    false
}

/* This function walks the code of a single predicate, supposed to
 * begin in code at the offset p. Each instruction is passed to the
 * walker function.
 */
pub(crate) fn walk_code(code: &Code, p: usize, mut walker: impl FnMut(&Line)) {
    let mut stack = vec![p];
    let mut visited_indices = IndexSet::new();

    while let Some(first_index) = stack.pop() {
        if visited_indices.contains(&first_index) {
            continue;
        } else {
            visited_indices.insert(first_index);
        }

        for (index, instr) in code[first_index..].iter().enumerate() {
            walker(instr);

            if capture_offset(instr, first_index + index, &mut stack) {
                break;
            }
        }
    }
}

/* A function for code walking that might result in modification to
 * the code. Otherwise identical to walk_code.
 */
/*
pub(crate) fn walk_code_mut(code: &mut Code, p: usize, mut walker: impl FnMut(&mut Line))
{
    let mut queue = VecDeque::from(vec![p]);

    while let Some(first_idx) = queue.pop_front() {
        let mut last_idx = first_idx;

        capture_next_range(code, &mut queue, &mut last_idx);

        for instr in &mut code[first_idx .. last_idx + 1] {
            walker(instr);
        }
    }
}
*/
