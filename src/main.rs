mod l0;

use l0::ast::{TopLevel};
use l0::codegen::{compile_target};
use l0::machine::{Machine};

use std::io::{self, Write};

fn l0_repl() {
    let mut ms = Machine::new();
    
    loop {
        print!("l0> ");
        
        let _ = io::stdout().flush();
        let mut buffer = String::new();
        
        io::stdin().read_line(&mut buffer).unwrap();
        
        let result = l0::parser::parse_top_level(&*buffer);

        if &*buffer == "quit\n" {
            break;
        } else if &*buffer == "clear\n" {
            ms = Machine::new();
        }        
        
        match result {            
            Ok(TopLevel::Fact(fact)) => {                
                let program = compile_target(&fact);
                                
                ms = Machine::new();                
                ms.program = Some(program);                
                
                println!("Program stored.");
            },
            Ok(TopLevel::Query(query)) => {
                if let Some(program) = ms.program.take() {                
                    let query = compile_target(&query);
                    
                    for instruction in &query {
                        ms.execute_query_instr(instruction);
                    }

                    for instruction in &program {                    
                        ms.execute_fact_instr(instruction);

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
