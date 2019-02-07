#[macro_use] extern crate downcast;
#[macro_use] extern crate prolog_parser;
extern crate termion;

use prolog::instructions::*;

mod prolog;

use prolog::compile::*;
use prolog::machine::*;
use prolog::read::*;
use prolog::toplevel::string_to_toplevel;
use prolog::write::*;

use std::io::{Write, stdin, stdout};

#[cfg(test)]
mod tests;

fn prolog_repl() {
    let mut wam = Machine::new();
    
    loop {
        print!("prolog> ");
        stdout().flush().unwrap();
        
        match toplevel_read_line() {
            Ok(Input::TermString(buffer)) => {
                let stdin  = stdin();
                let result = match string_to_toplevel(stdin.lock(), buffer, &mut wam) {
                    Ok(packet) => compile_term(&mut wam, packet),
                    Err(e) => EvalSession::from(e)
                };

                print(&mut wam, result)
            },
            Ok(Input::Batch) => {
                let stdin  = stdin();
                let result = compile_user_module(&mut wam, stdin.lock());
                
                print(&mut wam, result);
            },
            Ok(Input::Quit) => break,
            Ok(Input::Clear) => {
                wam.clear();
                continue;
            },
            Err(e) => print(&mut wam, EvalSession::from(e))
        };

        wam.reset();
    }
}

fn main() {
    prolog_repl();
}
