use prolog::ast::*;
use prolog::codegen::*;
use prolog::debray_allocator::*;
use prolog::machine::*;
use prolog::prolog_parser::*;

use termion::raw::IntoRawMode;
use termion::input::TermRead;
use termion::event::Key;

use std::io::{Write, stdin, stdout};
use std::fmt;
use std::mem::swap;

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Constant::Atom(ref atom) =>
                write!(f, "{}", atom),
            &Constant::EmptyList =>
                write!(f, "[]"),
            &Constant::BlockNum(integer) =>
                write!(f, "u{}", integer)
        }
    }
}

impl fmt::Display for FactInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &FactInstruction::GetConstant(Level::Shallow, ref constant, ref r) =>
                write!(f, "get_constant {}, A{}", constant, r.reg_num()),
            &FactInstruction::GetConstant(Level::Deep, ref constant, ref r) =>
                write!(f, "get_constant {}, {}", constant, r),
            &FactInstruction::GetList(Level::Shallow, ref r) =>
                write!(f, "get_list A{}", r.reg_num()),
            &FactInstruction::GetList(Level::Deep, ref r) =>
                write!(f, "get_list {}", r),
            &FactInstruction::GetStructure(Level::Deep, ref name, ref arity, ref r) =>
                write!(f, "get_structure {}/{}, {}", name, arity, r),
            &FactInstruction::GetStructure(Level::Shallow, ref name, ref arity, ref r) =>
                write!(f, "get_structure {}/{}, A{}", name, arity, r.reg_num()),
            &FactInstruction::GetValue(ref x, ref a) =>
                write!(f, "get_value {}, A{}", x, a),
            &FactInstruction::GetVariable(ref x, ref a) =>
                write!(f, "fact:get_variable {}, A{}", x, a),
            &FactInstruction::UnifyConstant(ref constant) =>
                write!(f, "unify_constant {}", constant),
            &FactInstruction::UnifyVariable(ref r) =>
                write!(f, "unify_variable {}", r),
            &FactInstruction::UnifyLocalValue(ref r) =>
                write!(f, "unify_local_value {}", r),
            &FactInstruction::UnifyValue(ref r) =>
                write!(f, "unify_value {}", r),
            &FactInstruction::UnifyVoid(n) =>
                write!(f, "unify_void {}", n)
        }
    }
}

impl fmt::Display for QueryInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &QueryInstruction::GetVariable(ref x, ref a) =>
                write!(f, "query:get_variable {}, A{}", x, a),
            &QueryInstruction::PutConstant(Level::Shallow, ref constant, ref r) =>
                write!(f, "put_constant {}, A{}", constant, r.reg_num()),
            &QueryInstruction::PutConstant(Level::Deep, ref constant, ref r) =>
                write!(f, "put_constant {}, {}", constant, r),
            &QueryInstruction::PutList(Level::Shallow, ref r) =>
                write!(f, "put_list A{}", r.reg_num()),
            &QueryInstruction::PutList(Level::Deep, ref r) =>
                write!(f, "put_list {}", r),
            &QueryInstruction::PutStructure(Level::Deep, ref name, ref arity, ref r) =>
                write!(f, "put_structure {}/{}, {}", name, arity, r),
            &QueryInstruction::PutStructure(Level::Shallow, ref name, ref arity, ref r) =>
                write!(f, "put_structure {}/{}, A{}", name, arity, r.reg_num()),
            &QueryInstruction::PutUnsafeValue(y, a) =>
                write!(f, "put_unsafe_value Y{}, A{}", y, a),
            &QueryInstruction::PutValue(ref x, ref a) =>
                write!(f, "put_value {}, A{}", x, a),
            &QueryInstruction::PutVariable(ref x, ref a) =>
                write!(f, "put_variable {}, A{}", x, a),
            &QueryInstruction::SetConstant(ref constant) =>
                write!(f, "set_constant {}", constant),
            &QueryInstruction::SetLocalValue(ref r) =>
                write!(f, "set_local_value {}", r),
            &QueryInstruction::SetVariable(ref r) =>
                write!(f, "set_variable {}", r),
            &QueryInstruction::SetValue(ref r) =>
                write!(f, "set_value {}", r),
            &QueryInstruction::SetVoid(n) =>
                write!(f, "set_void {}", n)
        }
    }
}

impl fmt::Display for ControlInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &ControlInstruction::Allocate(num_cells) =>
                write!(f, "allocate {}", num_cells),
            &ControlInstruction::Call(ref name, arity, pvs) =>
                write!(f, "call {}/{}, {}", name, arity, pvs),
            &ControlInstruction::CallN(arity) =>
                write!(f, "call_N {}", arity),
            &ControlInstruction::CatchCall =>
                write!(f, "call_catch"),
            &ControlInstruction::CatchExecute =>
                write!(f, "execute_catch"),
            &ControlInstruction::ExecuteN(arity) =>
                write!(f, "execute_N {}", arity),
            &ControlInstruction::Deallocate =>
                write!(f, "deallocate"),
            &ControlInstruction::Execute(ref name, arity) =>
                write!(f, "execute {}/{}", name, arity),
            &ControlInstruction::Proceed =>
                write!(f, "proceed"),
            &ControlInstruction::ThrowCall =>
                write!(f, "call_throw"),
            &ControlInstruction::ThrowExecute =>
                write!(f, "execute_throw")
        }
    }
}

impl fmt::Display for IndexedChoiceInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &IndexedChoiceInstruction::Try(offset) =>
                write!(f, "try {}", offset),
            &IndexedChoiceInstruction::Retry(offset) =>
                write!(f, "retry {}", offset),
            &IndexedChoiceInstruction::Trust(offset) =>
                write!(f, "trust {}", offset)
        }
    }
}

impl fmt::Display for ChoiceInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &ChoiceInstruction::TryMeElse(offset) =>
                write!(f, "try_me_else {}", offset),
            &ChoiceInstruction::RetryMeElse(offset) =>
                write!(f, "retry_me_else {}", offset),
            &ChoiceInstruction::TrustMe =>
                write!(f, "trust_me")
        }
    }
}

impl fmt::Display for IndexingInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &IndexingInstruction::SwitchOnTerm(v, c, l, s) =>
                write!(f, "switch_on_term {}, {}, {}, {}", v, c, l, s),
            &IndexingInstruction::SwitchOnConstant(num_cs, _) =>
                write!(f, "switch_on_constant {}", num_cs),
            &IndexingInstruction::SwitchOnStructure(num_ss, _) =>
                write!(f, "switch_on_structure {}", num_ss)
        }
    }
}

impl fmt::Display for CutInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &CutInstruction::Cut(_) =>
                write!(f, "cut"),
            &CutInstruction::NeckCut(_) =>
                write!(f, "neck_cut"),
            &CutInstruction::GetLevel =>
                write!(f, "get_level")
        }
    }
}

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Level::Shallow => write!(f, "A"),
            &Level::Deep => write!(f, "X")
        }
    }
}

impl fmt::Display for VarReg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &VarReg::Norm(RegType::Perm(reg)) => write!(f, "Y{}", reg),
            &VarReg::Norm(RegType::Temp(reg)) => write!(f, "X{}", reg),
            &VarReg::ArgAndNorm(RegType::Perm(reg), arg) =>
                write!(f, "Y{} A{}", reg, arg),
            &VarReg::ArgAndNorm(RegType::Temp(reg), arg) =>
                write!(f, "X{} A{}", reg, arg)
        }
    }
}

impl fmt::Display for RegType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &RegType::Perm(val) => write!(f, "Y{}", val),
            &RegType::Temp(val) => write!(f, "X{}", val)
        }
    }
}

/*
// Wait until constexprs are supported in stable before trying to
// switch to this.

struct ClauseRewriter { field: fn(&mut Vec<Box<Term>>) -> QueryTerm }

impl Clone for ClauseRewriter {
    fn clone(&self) -> Self {
        ClauseRewriter { field: self.field }
    }
}

struct ClauseRewriters {
    rewriter_map: HashMap<&'static str, ClauseRewriter>
}

impl ClauseRewriters {
    fn new() -> Self {
        let mut rewriter_map =
            [("call", ClauseRewriter { field: rewrite_call_N })]//,
        //("catch", rewrite_catch),
        //("throw", rewrite_throw)]
            .iter().cloned().collect();

        ClauseRewriters { rewriter_map: rewriter_map }
    }

    fn get(&self, name: &str) -> Option<&ClauseRewriter> {
        self.rewriter_map.get(name)
    }
}
*/

fn rewrite_call_n(terms: &mut Vec<Box<Term>>) -> QueryTerm {
    let mut new_terms = Vec::with_capacity(0);
    swap(&mut new_terms, terms);

    QueryTerm::CallN(new_terms)
}

fn rewrite_catch(terms: &mut Vec<Box<Term>>) -> QueryTerm {
    let mut new_terms = Vec::with_capacity(0);
    swap(&mut new_terms, terms);

    QueryTerm::Catch(new_terms)
}

fn rewrite_throw(terms: &mut Vec<Box<Term>>) -> QueryTerm {
    let mut new_terms = Vec::with_capacity(0);
    swap(&mut new_terms, terms);

    QueryTerm::Throw(new_terms)
}

fn rewrite_clause(name: &Atom, terms: &mut Vec<Box<Term>>) -> Option<QueryTerm>
{
    if name == "call" {
        Some(rewrite_call_n(terms))
    } else if name == "catch" && terms.len() == 3 {
        Some(rewrite_catch(terms))
    } else if name == "throw" && terms.len() == 1 {
        Some(rewrite_throw(terms))
    } else {
        None
    }
}

pub fn parse_code(input: &str) -> Option<TopLevel>
{
    match parse_TopLevel(input) {
        Ok(mut tl) => {
            for query in tl.query_iter_mut() {
                let new_query = match query {
                    &mut QueryTerm::Term(Term::Clause(_, ref name, ref mut cts)) =>
                        rewrite_clause(name, cts),
                    &mut QueryTerm::Term(Term::Var(_, _)) =>
                        Some(QueryTerm::CallN(Vec::new())),
                    _ => None
                };

                if let Some(mut new_query) = new_query {
                    swap(&mut new_query, query);
                }
            }

            Some(tl)
        },
        Err(_) => None
    }
}

fn is_consistent(predicate: &Vec<PredicateClause>) -> bool {
    let name  = predicate.first().unwrap().name();
    let arity = predicate.first().unwrap().arity();

    for clause in predicate.iter().skip(1) {
        if !(name == clause.name() && arity == clause.arity()) {
            return false;
        }
    }

    true
}

#[allow(dead_code)]
pub fn print_code(code: &Code) {
    for clause in code {
        match clause {
            &Line::Fact(ref fact) =>
                for fact_instr in fact {
                    println!("{}", fact_instr);
                },
            &Line::BuiltIn(_) => {},
            &Line::Cut(ref cut) =>
                println!("{}", cut),
            &Line::Choice(ref choice) =>
                println!("{}", choice),
            &Line::Control(ref control) =>
                println!("{}", control),
            &Line::IndexedChoice(ref choice) =>
                println!("{}", choice),
            &Line::Indexing(ref indexing) =>
                println!("{}", indexing),
            &Line::Query(ref query) =>
                for query_instr in query {
                    println!("{}", query_instr);
                }
        }
    }
}

pub fn read() -> String {
    let _ = stdout().flush();

    let mut buffer = String::new();
    let mut result = String::new();

    let stdin = stdin();
    stdin.read_line(&mut buffer).unwrap();

    if &*buffer.trim() == ":{" {
        buffer.clear();

        stdin.read_line(&mut buffer).unwrap();

        while &*buffer.trim() != "}:" {
            result += buffer.as_str();
            buffer.clear();
            stdin.read_line(&mut buffer).unwrap();
        }
    } else {
        result = buffer;
    }

    result
}

pub fn eval<'a, 'b: 'a>(wam: &'a mut Machine, tl: &'b TopLevel) -> EvalSession<'b>
{
    match tl {
        &TopLevel::Predicate(ref clauses) => {
            let mut cg = CodeGenerator::<DebrayAllocator>::new();

            if is_consistent(clauses) {
                let compiled_pred = cg.compile_predicate(clauses);
                print_code(&compiled_pred);
                wam.add_predicate(clauses, compiled_pred)
            } else {
                let msg = r"Error: predicate is inconsistent.
Each predicate must have the same name and arity.";

                EvalSession::EntryFailure(String::from(msg))
            }
        },
        &TopLevel::Fact(ref fact) => {
            let mut cg = CodeGenerator::<DebrayAllocator>::new();

            let compiled_fact = cg.compile_fact(fact);
            wam.add_fact(fact, compiled_fact)
        },
        &TopLevel::Rule(ref rule) => {
            let mut cg = CodeGenerator::<DebrayAllocator>::new();

            let compiled_rule = cg.compile_rule(rule);
            print_code(&compiled_rule);
            wam.add_rule(rule, compiled_rule)
        },
        &TopLevel::Query(ref query) => {
            let mut cg = CodeGenerator::<DebrayAllocator>::new();

            let compiled_query = cg.compile_query(query);
            print_code(&compiled_query);
            wam.submit_query(compiled_query, cg.take_vars())
        }
    }
}

pub fn print(wam: &mut Machine, result: EvalSession) {
    match result {
        EvalSession::InitialQuerySuccess(alloc_locs, mut heap_locs) => {
            print!("true");

            if !wam.or_stack_is_empty() {
                print!(" ");
            }

            println!(".");

            if heap_locs.is_empty() {
                return;
            }

            loop {
                let mut result = EvalSession::QueryFailure;
                let bindings = wam.heap_view(&heap_locs);

                let stdin  = stdin();
                let mut stdout = stdout().into_raw_mode().unwrap();

                write!(stdout, "{}", bindings).unwrap();
                stdout.flush().unwrap();

                if !wam.or_stack_is_empty() {
                    stdout.flush().unwrap();

                    for c in stdin.keys() {
                        match c.unwrap() {
                            Key::Char(';') => {
                                write!(stdout, " ;\n\r").unwrap();
                                result = wam.continue_query(&alloc_locs, &mut heap_locs);
                                break;
                            },
                            Key::Char('.') => {
                                write!(stdout, " .\n\r").unwrap();
                                return;
                            },
                            _ => {}
                        }
                    }

                    if let &EvalSession::QueryFailure = &result {
                        write!(stdout, "false.\n\r").unwrap();
                        stdout.flush().unwrap();
                        return;
                    }
                } else {
                    break;
                }
            }

            write!(stdout(), ".\n").unwrap();
        },
        EvalSession::QueryFailure => println!("false."),
        EvalSession::EntryFailure(msg) => println!("{}", msg),
        _ => {}
    };
}
