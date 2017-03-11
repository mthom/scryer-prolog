use prolog::ast::*;
use prolog::codegen::*;
use prolog::prolog_parser::*;
use prolog::machine::*;

use termion::raw::IntoRawMode;
use termion::input::TermRead;
use termion::event::Key;

use std::io::{Write, stdin, stdout};
use std::fmt;

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Constant::Atom(ref atom) =>
                write!(f, "{}", atom),        
            &Constant::EmptyList =>
                write!(f, "[]")
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
                write!(f, "get_variable {}, A{}", x, a),
            &FactInstruction::UnifyConstant(ref constant) =>
                write!(f, "unify_constant {}", constant),
            &FactInstruction::UnifyVariable(ref r) =>
                write!(f, "unify_variable {}", r),
            &FactInstruction::UnifyValue(ref r) =>
                write!(f, "unify_value {}", r)
        }
    }
}

impl fmt::Display for QueryInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
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
            &QueryInstruction::PutValue(ref x, ref a) =>
                write!(f, "put_value {}, A{}", x, a),
            &QueryInstruction::PutVariable(ref x, ref a) =>
                write!(f, "put_variable {}, A{}", x, a),
            &QueryInstruction::SetConstant(ref constant) =>
                write!(f, "set_constant {}", constant),
            &QueryInstruction::SetVariable(ref r) =>
                write!(f, "set_variable {}", r),
            &QueryInstruction::SetValue(ref r) =>
                write!(f, "set_value {}", r)
        }
    }
}

impl fmt::Display for ControlInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &ControlInstruction::Allocate(num_cells) =>
                write!(f, "allocate {}", num_cells),
            &ControlInstruction::Call(ref name, ref arity) =>
                write!(f, "call {}/{}", name, arity),
            &ControlInstruction::Deallocate =>
                write!(f, "deallocate"),
            &ControlInstruction::Proceed =>
                write!(f, "proceed")
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
            &Line::Choice(ref choice) =>
                println!("{}", choice),
            &Line::Control(ref control) =>
                println!("{}", control),
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

pub fn eval(wam: &mut Machine, buffer: &str) -> EvalResult
{
    let result = parse_TopLevel(buffer);
    let mut cg = CodeGenerator::new();

    match &result {
        &Ok(TopLevel::Predicate(ref clauses)) => {
            if is_consistent(clauses) {
                let compiled_pred = cg.compile_predicate(clauses);
                wam.add_predicate(clauses, compiled_pred);                

                EvalResult::EntrySuccess
            } else {
                let msg = r"Error: predicate is inconsistent.
Each predicate must have the same name and arity.";

                println!("{}", msg);
                EvalResult::EntryFailure
            }
        },
        &Ok(TopLevel::Fact(ref fact)) => {
            let compiled_fact = cg.compile_fact(&fact);
            wam.add_fact(fact, compiled_fact);
            EvalResult::EntrySuccess
        },
        &Ok(TopLevel::Rule(ref rule)) => {
            let compiled_rule = cg.compile_rule(&rule);
            wam.add_rule(rule, compiled_rule);
            EvalResult::EntrySuccess
        },
        &Ok(TopLevel::Query(ref query)) => {
            let compiled_query = cg.compile_query(&query);
            wam.run_query(compiled_query, &cg)            
        },
        &Err(_) => {
            println!("Grammatical error of some kind!");
            EvalResult::EntryFailure
        }
    }
}

pub fn print(wam: &mut Machine, result: EvalResult) {
    match result {
        EvalResult::InitialQuerySuccess(heap_locs) => {
            println!("yes");

            if heap_locs.is_empty() {
                return;
            }

            'outer: loop {
                let mut result = EvalResult::QueryFailure;
                let bindings = wam.heap_view(&heap_locs);
                
                let stdin  = stdin();
                let mut stdout = stdout().into_raw_mode().unwrap();

                write!(stdout, "{}\n\r", bindings).unwrap();
                stdout.flush().unwrap();

                if !wam.or_stack_is_empty() {
                    write!(stdout, "Press ; to continue or . to abort.\n\r").unwrap();
                    stdout.flush().unwrap();

                    for c in stdin.keys() {
                        match c.unwrap() {
                            Key::Char(';') => {
                                result = wam.continue_query();
                                break;
                            },
                            Key::Char('.') =>
                                break 'outer,
                            _ => {}
                        }
                    };

                    if let &EvalResult::QueryFailure = &result {
                        write!(stdout, "no\n\r").unwrap();
                        stdout.flush().unwrap();
                        break;
                    }
                } else {
                    break;
                }
            }
        },
        EvalResult::QueryFailure => println!("no"),
        _ => {}
    };
}
