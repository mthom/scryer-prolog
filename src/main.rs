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
                let name  = fact.name().to_owned();
                let arity = fact.arity();
                let fact  = compile_fact(&fact);

                ms.add_fact(fact, name, arity);
            },
            Ok(TopLevel::Query(query)) => {
                let compiled_query = compile_query(&query);
                
                ms.execute_query(&compiled_query);
                
                if ms.failed() {
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
