use crate::instructions::*;

use indexmap::IndexSet;

fn capture_offset(line: &Instruction, index: usize, stack: &mut Vec<usize>) -> bool {
    match line {
        &Instruction::TryMeElse(offset) if offset > 0 => {
            stack.push(index + offset);
        }
        &Instruction::DefaultRetryMeElse(offset) |
        &Instruction::RetryMeElse(offset)
            if offset > 0 =>
        {
            stack.push(index + offset);
        }
        &Instruction::DynamicElse(_, _, NextOrFail::Next(offset))
            if offset > 0 =>
        {
            stack.push(index + offset);
        }
        &Instruction::DynamicInternalElse(_, _, NextOrFail::Next(offset))
            if offset > 0 =>
        {
            stack.push(index + offset);
        }
        &Instruction::JmpByCall(offset) => {
            stack.push(index + offset);
        }
        &Instruction::Proceed => {
            return true;
        }
        &Instruction::RevJmpBy(offset) => {
            if offset > 0 {
                stack.push(index - offset);
            } else {
                return true;
            }
        }
        instr if instr.is_execute() => {
            return true;
        }
        _ => {}
    };

    false
}

/* This function walks the code of a single predicate, supposed to
 * begin in code at the offset p. Each instruction is passed to the
 * walker function.
 */
pub(crate) fn walk_code(code: &Code, p: usize, mut walker: impl FnMut(&Instruction)) {
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
