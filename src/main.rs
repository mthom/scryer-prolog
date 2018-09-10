#[macro_use] extern crate downcast;
#[macro_use] extern crate prolog_parser;
extern crate termion;

use prolog::instructions::*;

mod prolog;

use prolog::compile::*;
use prolog::machine::*;
use prolog::read::*;
use prolog::write::*;

use std::io::{Write, stdout};

#[cfg(test)]
mod tests;

fn parse_and_compile_line(wam: &mut Machine, buffer: &str)
{
    match parse_code(wam, buffer) {
        Ok(packet) => {
            let result = compile_packet(wam, packet);
            print(wam, result);
        },
        Err(e) => print(wam, EvalSession::from(e))
    }
}

fn prolog_repl() {
    let mut wam = Machine::new();

    loop {
        print!("prolog> ");
        stdout().flush().unwrap();
        
        match read_toplevel(&mut wam) {
            Ok(Input::Term(term)) =>
                match compile_term(&mut wam, term) {
                    Ok(packet) => {
                        let result = compile_packet(&mut wam, packet);
                        print(&mut wam, result);
                    },
                    Err(e) => print(&mut wam, EvalSession::from(e))
                },
            Ok(Input::Line(line)) => parse_and_compile_line(&mut wam, line.as_str()),
            Ok(Input::Batch(batch)) => {
                let result = compile_user_module(&mut wam, batch.as_bytes());
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
