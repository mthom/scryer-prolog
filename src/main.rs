#[macro_use] extern crate lazy_static;
extern crate termion;

mod prolog;
#[macro_use] mod test_utils;

use prolog::io::*;
use prolog::machine::*;
use prolog::parser::toplevel::*;

#[cfg(test)]
mod tests;

fn process_buffer(wam: &mut Machine, buffer: &str)
{
    match parse_code(buffer, wam.op_dir()) {
        Ok(tl) => {
            let result = eval(wam, &tl);
            print(wam, result);
        },
        Err(s) => println!("{:?}", s)
    };
}

fn prolog_repl() {
    let mut wam = Machine::new();

    loop {
        print!("prolog> ");

        let buffer = read();

        if buffer == "quit\n" {
            break;
        } else if buffer == "clear\n" {
            wam.clear();
            continue;
        }

        process_buffer(&mut wam, buffer.as_str());
        wam.reset();
    }
}

fn main() {
    prolog_repl();
}
