mod l0;

use l0::ast::{Atom, Program, Term, TopLevel, Var};
use l0::codegen::{compile_fact, compile_query};
use l0::machine::{MachineState};

use std::io::{self, Write};

fn print_instructions(program : &Program) {
    for instruction in program {
        println!("{:}", instruction);        
    }
}

fn l0_repl<'a>() {
    let mut ms = MachineState::new();
    
    loop {
        print!("l0> ");
        io::stdout().flush();

        let mut buffer = String::new();
        io::stdin().read_line(&mut buffer).unwrap();
        
        let result = l0::l0_parser::parse_TopLevel(&*buffer);

        if &*buffer == "quit\n" {
            break;
        } else if &*buffer == "clear\n" {
            ms = MachineState::new();
        }        
        
        match result {            
            Ok(TopLevel::Fact(fact)) => {                
                let program = compile_fact(&fact);
                
                ms = MachineState::new();                
                ms.program = Some(program);                
                
                println!("Program stored.");
            },
            Ok(TopLevel::Query(query)) => {
                if let Some(program) = ms.program.take() {                
                    let query = compile_query(&query);
                    
                    for instruction in &query {
                        ms.execute(instruction);
                    }

                    for instruction in &program {                    
                        ms.execute(instruction);

                        if ms.fail {                            
                            break;
                        }
                    }                    
                
                    if ms.fail {
                        println!("no");
                    } else {
                        println!("yes");
                    }

                    ms.reset_heap();
                    ms.program = Some(program);
                } else {
                    println!("No program to speak of.");
                }
            },                                        
            Err(_) => println!("Grammatical error of some kind!"),
        };        
    }
}

fn main() {
    l0_repl();
}
