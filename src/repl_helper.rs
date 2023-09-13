use rustyline::completion::Completer;
use rustyline::highlight::{Highlighter, MatchingBracketHighlighter};
use rustyline::hint::Hinter;
use rustyline::validate::Validator;
use rustyline::{Context, Helper as RlHelper, Result};

use std::sync::Weak;

use crate::atom_table::{AtomString, AtomTable, STATIC_ATOMS_MAP};

// TODO: Maybe add validation to the helper
pub struct Helper {
    highligher: MatchingBracketHighlighter,
    pub atoms: Weak<AtomTable>,
}

impl Helper {
    pub fn new() -> Self {
        Self {
            highligher: MatchingBracketHighlighter::new(),
            atoms: Weak::new(),
        }
    }
}

impl RlHelper for Helper {}

fn get_prefix(line: &str, pos: usize) -> Option<usize> {
    let mut start_of_atom = None;
    let mut first_letter = true;

    for (i, char) in line.chars().enumerate() {
        if first_letter {
            if char.is_alphabetic() && char.is_lowercase() {
                start_of_atom = Some(i);
            }

            first_letter = false;
        }

        if !char.is_alphanumeric() && char != '_' {
            first_letter = true;
            start_of_atom = None;
        }

        if i == pos {
            break;
        }
    }

    if first_letter || pos == 0 {
        start_of_atom = Some(pos)
    }

    start_of_atom
}

impl Completer for Helper {
    type Candidate = AtomString<'static>;

    fn complete(
        &self,
        line: &str,
        pos: usize,
        _ctx: &Context<'_>,
    ) -> Result<(usize, Vec<Self::Candidate>)> {
        let start_of_prefix = get_prefix(line, pos);
        if let Some(idx) = start_of_prefix {
            let sub_str = line.get(idx..pos).unwrap();

            let atom_table = self.atoms.upgrade().unwrap();

            let index_set = atom_table.active_table();

            let mut matching = index_set
                .iter()
                .chain(STATIC_ATOMS_MAP.values())
                .map(|a| a.as_str())
                .filter(|a| a.starts_with(sub_str))
                .collect::<Vec<_>>();

            matching.sort_unstable_by(|a, b| Ord::cmp(&a.len(), &b.len()));

            Ok((idx, matching))
        } else {
            Ok((0, vec![]))
        }
    }
}

impl Highlighter for Helper {
    fn highlight<'l>(&self, line: &'l str, pos: usize) -> std::borrow::Cow<'l, str> {
        self.highligher.highlight(line, pos)
    }

    fn highlight_char(&self, line: &str, pos: usize) -> bool {
        self.highligher.highlight_char(line, pos)
    }
}

impl Validator for Helper {}

impl Hinter for Helper {
    type Hint = String;
}
