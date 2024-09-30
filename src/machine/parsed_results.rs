use crate::atom_table::*;
use crate::heap_iter::{stackful_post_order_iter, NonListElider};
use crate::machine::{F64Offset, F64Ptr, Fixnum, HeapCellValueTag};
use crate::parser::ast::{Var, VarPtr};
use dashu::*;
use indexmap::IndexMap;
use ordered_float::OrderedFloat;
use std::cmp::Ordering;
use std::collections::BTreeMap;

use super::Machine;
use super::{HeapCellValue, Number};

/// Represents a leaf answer from a query.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LeafAnswer {
    True,
    False,
    Exception(PrologTerm),
    LeafAnswer {
        bindings: BTreeMap<String, PrologTerm>,
        residual_goals: Vec<PrologTerm>,
    },
}

/// Represents a Prolog term.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PrologTerm {
    Integer(Integer),
    Rational(Rational),
    Float(OrderedFloat<f64>),
    Atom(String),
    String(String),
    List(Vec<PrologTerm>),
    Structure(String, Vec<PrologTerm>),
    Var(String),
}

/// This is an auxiliary function to turn a count into names of anonymous variables like _A, _B,
/// _AB, etc...
fn count_to_letter_code(mut count: usize) -> String {
    let mut letters = Vec::new();

    loop {
        let letter_idx = (count % 26) as u32;
        letters.push(char::from_u32('A' as u32 + letter_idx).unwrap());
        count /= 26;

        if count == 0 {
            break;
        }
    }

    letters.into_iter().chain("_".chars()).rev().collect()
}

impl PrologTerm {
    pub(crate) fn from_heapcell(
        machine: &mut Machine,
        heap_cell: HeapCellValue,
        var_names: &mut IndexMap<HeapCellValue, VarPtr>,
    ) -> Self {
        // Adapted from MachineState::read_term_from_heap
        let mut term_stack = vec![];
        let iter = stackful_post_order_iter::<NonListElider>(
            &mut machine.machine_st.heap,
            &mut machine.machine_st.stack,
            heap_cell,
        );

        let mut anon_count: usize = 0;
        let var_ptr_cmp = |a, b| match a {
            Var::Named(name_a) => match b {
                Var::Named(name_b) => name_a.cmp(&name_b),
                _ => Ordering::Less,
            },
            _ => match b {
                Var::Named(_) => Ordering::Greater,
                _ => Ordering::Equal,
            },
        };

        for addr in iter {
            let addr = unmark_cell_bits!(addr);

            read_heap_cell!(addr,
                (HeapCellValueTag::Lis) => {
                    let tail = term_stack.pop().unwrap();
                    let head = term_stack.pop().unwrap();

                    let list = match tail {
                        PrologTerm::Atom(atom) if atom == "[]" => match head {
                            PrologTerm::Atom(ref a) if a.chars().collect::<Vec<_>>().len() == 1 => {
                                // Handle lists of char as strings
                                PrologTerm::String(a.to_string())
                            }
                            _ => PrologTerm::List(vec![head]),
                        },
                        PrologTerm::List(elems) if elems.is_empty() => match head {
                            PrologTerm::Atom(ref a) if a.chars().collect::<Vec<_>>().len() == 1 => {
                                // Handle lists of char as strings
                                PrologTerm::String(a.to_string())
                            },
                            _ => PrologTerm::List(vec![head]),
                        },
                        PrologTerm::List(mut elems) => {
                            elems.insert(0, head);
                            PrologTerm::List(elems)
                        },
                        PrologTerm::String(mut elems) => match head {
                            PrologTerm::Atom(ref a) if a.chars().collect::<Vec<_>>().len() == 1 => {
                                // Handle lists of char as strings
                                elems.insert(0, a.chars().next().unwrap());
                                PrologTerm::String(elems)
                            },
                            _ => {
                                let mut elems: Vec<PrologTerm> = elems
                                    .chars()
                                    .map(|x| PrologTerm::Atom(x.into()))
                                    .collect();
                                elems.insert(0, head);
                                PrologTerm::List(elems)
                            }
                        },
                        _ => {
                            PrologTerm::Structure(".".into(), vec![head, tail])
                        }
                    };
                    term_stack.push(list);
                }
                (HeapCellValueTag::Var | HeapCellValueTag::AttrVar | HeapCellValueTag::StackVar) => {
                    let var = var_names.get(&addr).map(|x| x.borrow().clone());
                    match var {
                        Some(Var::Named(name)) => term_stack.push(PrologTerm::Var(name)),
                        _ => {
                            let anon_name = loop {
                                // Generate a name for the anonymous variable
                                let anon_name = count_to_letter_code(anon_count);

                                // Find if this name is already being used
                                var_names.sort_by(|_, a, _, b| {
                                    var_ptr_cmp(a.borrow().clone(), b.borrow().clone())
                                });
                                let binary_result = var_names.binary_search_by(|_,a| {
                                    let var_ptr = Var::Named(anon_name.clone());
                                    var_ptr_cmp(a.borrow().clone(), var_ptr.clone())
                                });

                                match binary_result {
                                    Ok(_) => anon_count += 1, // Name already used
                                    Err(_) => {
                                        // Name not used, assign it to this variable
                                        let var_ptr = VarPtr::from(Var::Named(anon_name.clone()));
                                        var_names.insert(addr, var_ptr);
                                        break anon_name;
                                    },
                                }
                            };
                            term_stack.push(PrologTerm::Var(anon_name));
                        },
                    }
                }
                (HeapCellValueTag::F64, f) => {
                    term_stack.push(PrologTerm::Float(*f));
                }
                (HeapCellValueTag::Char, c) => {
                    term_stack.push(PrologTerm::Atom(c.into()));
                }
                (HeapCellValueTag::Fixnum, n) => {
                    term_stack.push(PrologTerm::Integer(n.into()));
                }
                (HeapCellValueTag::Cons) => {
                    match Number::try_from(addr) {
                        Ok(Number::Integer(i)) => term_stack.push(PrologTerm::Integer((*i).clone())),
                        Ok(Number::Rational(r)) => term_stack.push(PrologTerm::Rational((*r).clone())),
                        _ => {}
                    }
                }
                (HeapCellValueTag::CStr, s) => {
                    term_stack.push(PrologTerm::String(s.as_str().to_string()));
                }
                (HeapCellValueTag::Atom, (name, arity)) => {
                    //let h = iter.focus().value() as usize;
                    //let mut arity = arity;

                    // Not sure why/if this is needed.
                    // Might find out with better testing later.
                    /*
                    if iter.heap.len() > h + arity + 1 {
                        let value = iter.heap[h + arity + 1];

                        if let Some(idx) = get_structure_index(value) {
                            // in the second condition, arity == 0,
                            // meaning idx cannot pertain to this atom
                            // if it is the direct subterm of a larger
                            // structure.
                            if arity > 0 || !iter.direct_subterm_of_str(h) {
                                term_stack.push(
                                    Term::Literal(Cell::default(), Literal::CodeIndex(idx))
                                );

                                arity += 1;
                            }
                        }
                    }
                    */

                    if arity == 0 {
                        let atom_name = name.as_str().to_string();
                        if atom_name == "[]" {
                            term_stack.push(PrologTerm::List(vec![]));
                        } else {
                            term_stack.push(PrologTerm::Atom(atom_name));
                        }
                    } else {
                        let subterms = term_stack
                            .drain(term_stack.len() - arity ..)
                            .collect();

                        term_stack.push(PrologTerm::Structure(name.as_str().to_string(), subterms));
                    }
                }
                (HeapCellValueTag::PStr, atom) => {
                    let tail = term_stack.pop().unwrap();

                    match tail {
                        PrologTerm::Atom(atom) => {
                            if atom == "[]" {
                                term_stack.push(PrologTerm::String(atom.as_str().to_string()));
                            }
                        },
                        PrologTerm::List(l) => {
                            let mut list: Vec<PrologTerm> = atom
                                .as_str()
                                .to_string()
                                .chars()
                                .map(|x| PrologTerm::Atom(x.to_string()))
                                .collect();
                            list.extend(l.into_iter());
                            term_stack.push(PrologTerm::List(list));
                        },
                        _ => {
                            let mut list: Vec<PrologTerm> = atom
                                .as_str()
                                .to_string()
                                .chars()
                                .map(|x| PrologTerm::Atom(x.to_string()))
                                .collect();

                            let mut partial_list = PrologTerm::Structure(
                                ".".into(),
                                vec![
                                    list.pop().unwrap(),
                                    tail,
                                ],
                            );

                            while let Some(last) = list.pop() {
                                partial_list = PrologTerm::Structure(
                                    ".".into(),
                                    vec![
                                        last,
                                        partial_list,
                                    ],
                                );
                            }

                            term_stack.push(partial_list);
                        }
                    }
                }
                // I dont know if this is needed here.
                /*
                (HeapCellValueTag::PStrLoc, h) => {
                    let atom = cell_as_atom_cell!(iter.heap[h]).get_name();
                    let tail = term_stack.pop().unwrap();

                    term_stack.push(Term::PartialString(
                        Cell::default(),
                        atom.as_str().to_owned(),
                        Box::new(tail),
                    ));
                }
                */
                _ => {
                }
            );
        }

        debug_assert_eq!(term_stack.len(), 1);
        term_stack.pop().unwrap()
    }
}
