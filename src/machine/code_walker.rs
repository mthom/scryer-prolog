use crate::instructions::*;

use fxhash::FxBuildHasher;
use indexmap::IndexSet;

fn capture_offset(line: &Instruction, index: usize, stack: &mut Vec<usize>) -> bool {
    match line {
        &Instruction::TryMeElse(offset) if offset > 0 => {
            stack.push(index + offset);
        }
        &Instruction::DefaultRetryMeElse(offset) | &Instruction::RetryMeElse(offset) if offset > 0 => {
            stack.push(index + offset);
        }
        &Instruction::DynamicElse(_, _, NextOrFail::Next(offset)) if offset > 0 => {
            stack.push(index + offset);
        }
        &Instruction::DynamicInternalElse(_, _, NextOrFail::Next(offset)) if offset > 0 => {
            stack.push(index + offset);
        }
        &Instruction::Proceed | &Instruction::JmpByCall(_) => {
            return true;
        }
        &Instruction::RevJmpBy(offset) => {
            if offset > 0 {
                stack.push(index - offset);
            }

            return true;
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
    let mut visited_indices = IndexSet::with_hasher(FxBuildHasher::default());

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
