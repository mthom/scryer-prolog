mod l2;

use l2::ast::*;
use l2::codegen::*;
use l2::machine::*;

use std::io::{self, Write};

fn l2_repl() {
    let mut wam = Machine::new();

    loop {
        print!("l2> ");

        let _ = io::stdout().flush();
        let mut buffer = String::new();

        io::stdin().read_line(&mut buffer).unwrap();

        let result = l2::l2_parser::parse_TopLevel(&*buffer);

        if &*buffer == "quit\n" {
            break;
        } else if &*buffer == "clear\n" {
            wam = Machine::new();
            continue;
        }

        let mut cg = CodeGenerator::new();

        match &result {
            &Ok(TopLevel::Fact(ref fact)) => {
                let compiled_fact = cg.compile_fact(&fact);
                wam.add_fact(fact, compiled_fact);
            },
            &Ok(TopLevel::Rule(ref rule)) => {
                let compiled_rule = cg.compile_rule(&rule);
                wam.add_rule(rule, compiled_rule);
            },
            &Ok(TopLevel::Query(ref query)) => {
                let compiled_query = cg.compile_query(&query);
                let output = wam.run_query(compiled_query, &cg);

                match output {
                    Some(result) => {
                        println!("yes");

                        if result != "" {
                            println!("{}", result);
                        }
                    },
                    None => println!("no")
                }
            },
            &Err(_) => println!("Grammatical error of some kind!"),
        };
    }
}

fn main() {
    l2_repl();
}
