use indexmap::IndexSet;
use rustyline::completion::{Candidate, Completer};
use rustyline::highlight::{Highlighter, MatchingBracketHighlighter};
use rustyline::hint::Hinter;
use rustyline::validate::Validator;
use rustyline::{Context, Helper as RlHelper, Result};

use crate::atom_table::{Atom, STATIC_ATOMS_MAP};

// TODO: Maybe add validation to the helper
pub struct Helper {
    highligher: MatchingBracketHighlighter,
    pub atoms: *const IndexSet<Atom>,
}

impl Helper {
    pub fn new() -> Self {
        Self {
            highligher: MatchingBracketHighlighter::new(),
            atoms: std::ptr::null(),
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

pub struct StrPtr(*const str);

impl Candidate for StrPtr {
    fn display(&self) -> &str {
        unsafe { self.0.as_ref().unwrap() }
    }

    fn replacement(&self) -> &str {
        unsafe { self.0.as_ref().unwrap() }
    }
}

impl Completer for Helper {
    type Candidate = StrPtr;

    fn complete(
        &self,
        line: &str,
        pos: usize,
        _ctx: &Context<'_>,
    ) -> Result<(usize, Vec<Self::Candidate>)> {
        let start_of_prefix = get_prefix(line, pos);
        if let Some(idx) = start_of_prefix {
            let sub_str = line.get(idx..pos).unwrap();
            Ok((idx, unsafe {
                let mut matching = (*self.atoms)
                    .iter()
                    .chain(STATIC_ATOMS_MAP.values())
                    .filter(|a| a.as_str().starts_with(sub_str))
                    .map(|s| StrPtr(s.as_str()))
                    .collect::<Vec<_>>();

                matching.sort_unstable_by(|a, b| Ord::cmp(&(*a.0).len(), &(*b.0).len()));
                matching
            }))
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
