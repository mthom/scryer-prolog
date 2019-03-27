#[macro_use] extern crate cfg_if;
#[macro_use] extern crate downcast;
#[macro_use] extern crate prolog_parser;
#[macro_use] extern crate ref_thread_local;

cfg_if! {
    if #[cfg(feature = "readline_rs_compat")] {
        extern crate readline_rs_compat;
    }
}

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
        #[cfg(feature = "readline_rs_compat")]
        readline::set_line_mode(readline::LineMode::Single);

        match toplevel_read_line() {
            Ok(Input::TermString(buffer)) => {
                let result = match string_to_toplevel(buffer.as_bytes(), &mut wam) {
                    Ok(packet) => compile_term(&mut wam, packet),
                    Err(e) => EvalSession::from(e)
                };

                print(&mut wam, result)
            },
            Ok(Input::Batch) => {
                #[cfg(feature = "readline_rs_compat")]
                readline::set_line_mode(readline::LineMode::Multi);

                let src = match readline::read_batch("") {
                    Ok(src) => src,
                    Err(e) => {
                        println!("{}", e);
                        continue;
                    }
                };

                let result = compile_user_module(&mut wam, &src[0 ..]);
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
    #[cfg(feature = "readline_rs_compat")]
    readline::readline_initialize();
    prolog_repl();
}
