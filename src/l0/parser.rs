use l0::ast::{Term, TopLevel, Var};
use l0::l0_parser::{parse_TopLevel};

use std::collections::{HashMap};

extern crate lalrpop_util as __lalrpop_util;

pub type ParseResult<'a> =
    Result<TopLevel, __lalrpop_util::ParseError<usize,(usize, &'a str),()>>;

pub fn parse_top_level<'a>(input: &'a str) -> ParseResult {
    let result = parse_TopLevel(&*input);
    
    if let Ok(result) = result {
        return Ok(mark_cells(result));
    }

    result
}

#[inline]
fn mark_cells(tl: TopLevel) -> TopLevel {
    match tl {
        TopLevel::Fact(term) => TopLevel::Fact(mark_term_cells(term)),
        TopLevel::Query(term) => TopLevel::Query(mark_term_cells(term))            
    }
}
    
fn mark_term_cells(term: Term) -> Term {
    let mut cell_num = 1;    
    
    {
        let mut bindings: HashMap<&Var, usize> = HashMap::new();
        let mut iter = term.breadth_first_iter();
    
        while let Some(term) = iter.next() {
            if let &Term::Var(ref cell, ref var) = term {
                let cell_num_in_map = bindings.entry(var).or_insert(cell_num);
                
                if *cell_num_in_map != cell_num {                    
                    cell.set(*cell_num_in_map);
                    continue;
                }
            }

            term.set_cell(cell_num);
            cell_num += 1;
        }
    }

    term
}
