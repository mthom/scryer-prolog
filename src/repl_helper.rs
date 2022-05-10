use rustyline::completion::Completer;
use rustyline::hint::Hinter;
use rustyline::validate::Validator;
use rustyline::highlight::{MatchingBracketHighlighter, Highlighter};
use rustyline::{Helper as RlHelper, Result, Context};

// pub struct Atoms {
//     atoms: *const *const str,
//     len: usize,
// }

// impl Atoms {
//     pub fn new() -> Self {
//         Self {
//             atoms: std::ptr::null(),
//             len: 0,
//         }
//     }
// }

// pub struct AtomsIterator<'a> {
//     atoms: &'a Atoms,
//     idx: usize,
// }

// impl<'a> Iterator for AtomsIterator<'a> {
//     type Item = &'a str;

//     fn next(&mut self) -> Option<Self::Item> {
//         self.idx += 1;

//         if self.idx == self.atoms.len {
//             None
//         } else {
//             unsafe {
//                 let next = self.atoms.atoms.offset(self.idx as isize);
//                 (*next).as_ref()
//             }
//         }
//     }
// }

// impl<'a> IntoIterator for &'a Atoms {
//     type Item = &'a str;
//     type IntoIter = AtomsIterator<'a>;

//     fn into_iter(self) -> Self::IntoIter {
//         Self::IntoIter {
//             atoms: self,
//             idx: 0,
//         }
//     }
// }

// TODO: Maybe add validation to the helper
pub struct Helper {
    highligher: MatchingBracketHighlighter,
    pub atoms: Vec<String>,
}

impl Helper {
    pub fn new() -> Self {
        Self {
            highligher: MatchingBracketHighlighter::new(),
            atoms: vec![],
        }
    }

    // pub fn set_atoms(&mut self, atoms_ptr: *const *const str, len: usize) {
    //     self.atoms.atoms = atoms_ptr;
    //     self.atoms.len = len;
    // }
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
            break
        }
    }

    if first_letter || pos == 0 {
        start_of_atom = Some(pos)
    }

    start_of_atom
}

impl Completer for Helper {
    type Candidate = String;

    fn complete(&self, line: &str, pos: usize, _ctx: &Context<'_>) -> Result<(usize, Vec<Self::Candidate>)> {
        let start_of_prefix = get_prefix(line, pos);
        if let Some(idx) = start_of_prefix {
            let sub_str = line.get(idx..pos).unwrap();
            let matching = self.atoms.iter().filter(|a| a.starts_with(sub_str)).map(|s| s.to_string()).collect();
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
