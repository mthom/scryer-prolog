#[macro_use] extern crate downcast;
#[macro_use] extern crate prolog_parser;

extern crate readline_rs_compat;
extern crate termion;

mod prolog;

use prolog::machine::*;
use prolog::machine::compile::*;
use prolog::machine::machine_errors::*;
use prolog::machine::toplevel::string_to_toplevel;
use prolog::read::*;
use prolog::write::*;

#[cfg(test)]
mod tests;

fn prolog_repl() {
    let mut wam = Machine::new();

    loop {
        set_line_mode(LineMode::Single);

        match toplevel_read_line() {
            Ok(Input::TermString(buffer)) => {
                let result = match string_to_toplevel(buffer.as_bytes(), &mut wam) {
                    Ok(packet) => compile_term(&mut wam, packet),
                    Err(e) => EvalSession::from(e)
                };

                print(&mut wam, result)
            },
            Ok(Input::Batch) => {
                set_line_mode(LineMode::Multi);

                let src = match read_batch("") {
                    Ok(src) => src,
                    Err(e) => {
                        println!("{}", e);
                        continue;
                    }
                };
                
                let result = compile_user_module(&mut wam, src.as_bytes());
                print(&mut wam, result);
            },
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
    readline_initialize();
    prolog_repl();
}
