#![cfg(test)]
extern crate test_generator;

use core::panic;
use std::path::Path;

use crate::helper::run_top_level_test_with_args;
use scryer_prolog::machine::Machine;
use std::io::ErrorKind;
use test_generator::test_resources;

#[test_resources("src/tests/*.pl")]
#[test_resources("src/tests/issues/*.pl")]
#[test_resources("src/tests/clpz/*.pl")]
fn prolog_test(path: &str) {
    let (expected_input_path, expected_output_path) = {
        let mut i = Path::new(path).to_owned();
        let mut o = i.clone();
        i.set_extension("in");
        o.set_extension("out");
        (i, o)
    };

    let mut machine = Machine::with_test_streams();
    let mut output = machine.test_load_file(path);

    // Attempt 1: test_load_string() - this loads as a module file, not stdin
    // match std::fs::read_to_string(expected_input_path) {
    //     Ok(stdin) => output.extend(machine.test_load_string(&stdin)),
    //     Err(err) if err.kind() == ErrorKind::NotFound => {}
    //     _ => panic!("failed to read input file"),
    // };

    // Attempt 2: set_user_input() - doesn't seem to work
    match std::fs::read_to_string(expected_input_path) {
        Ok(stdin) => machine.set_user_input(stdin),
        Err(err) if err.kind() == ErrorKind::NotFound => {}
        _ => panic!("failed to read input file"),
    };

    // Attempt 3: run top level manually -- tests fail and time out
    // use scryer_prolog::{atom, atom_table::Atom}
    // machine.run_top_level(atom!("$toplevel"), (atom!("$repl"), 1));

    let mut output = String::from_utf8(output).unwrap();
    output.push_str(&machine.get_user_output()); // doesn't do anything?

    match std::fs::read_to_string(expected_output_path) {
        Ok(expected_output) => {
            assert_eq!(expected_output.trim(), output.trim(), "expected != actual")
        }
        Err(err) if err.kind() == ErrorKind::NotFound => assert_eq!("", output.trim()),
        _ => panic!("failed to read output file"),
    }
}

// issue #839
#[test]
fn op3() {
    run_top_level_test_with_args(["src/tests/cli/issue839-op3.pl", "-g", "halt"], "", "")
}

// issue #820
#[test]
fn multiple_goals() {
    run_top_level_test_with_args(
        [
            "-g",
            "test",
            "-g",
            "halt",
            "src/tests/cli/issue820-goals.pl",
        ],
        "",
        "helloworld\n",
    );
}

// issue #820
#[test]
fn compound_goal() {
    run_top_level_test_with_args(
        ["-g", "test,halt", "src/tests/cli/issue820-goals.pl"],
        "",
        "helloworld\n",
    )
}

/*
// issue #812
#[test] // FIXME: the line number is of by one (should be 4), empty line not accounted for or starting to count at line 0?
fn singleton_warning() {
    run_top_level_test_no_args(
        "['tests-pl/issue812-singleton-warning.pl'].\n\
         halt.\n",
        "\
        Warning: singleton variables X at line 3 of issue812-singleton-warning.pl\n   \
        true.\n\
        ",
    );
}
*/
