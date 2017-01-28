mod l1;

use l1::ast::TopLevel;
use l1::codegen::{compile_fact, compile_query};
use l1::machine::Machine;

use std::io::{self, Write};

fn l1_repl() {
    let mut ms = Machine::new();

    loop {
        print!("l1> ");

        let _ = io::stdout().flush();
        let mut buffer = String::new();

        io::stdin().read_line(&mut buffer).unwrap();

        let result = l1::l1_parser::parse_TopLevel(&*buffer);

        if &*buffer == "quit\n" {
            break;
        } else if &*buffer == "clear\n" {
            ms = Machine::new();
        }

        match result {
            Ok(TopLevel::Fact(fact)) => {
                let mut compiled_fact = compile_fact(&fact);
                let index = ms.code.len();

                ms.code.append(&mut compiled_fact);
                ms.code_dir.insert((fact.name().clone(), fact.arity()), index);
            },
            Ok(TopLevel::Query(query)) => {
                let compiled_query = compile_query(&query);
                
                for instruction in &compiled_query {
                    ms.execute_query_instr(instruction);

                    if ms.fail {
                        break;
                    }
                }

                if ms.fail {
                    println!("no");
                } else {
                    println!("yes");
                }

                ms.reset_machine_state();
            },
            Err(_) => println!("Grammatical error of some kind!"),
        };
    }
}

fn main() {
    l1_repl();
}
