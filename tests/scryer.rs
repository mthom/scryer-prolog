/// Loads the file and if some expected output is given checks that it matches
fn test_file(file: &str, expected: Option<&[u8]>) {
    use scryer_prolog::*;

    let input = machine::Stream::from("");
    let output = machine::Stream::from(String::new());

    let mut wam = machine::Machine::new(input, output.clone());

    wam.load_file(
        file.into(),
        machine::Stream::from(
            std::fs::read_to_string(AsRef::<std::path::Path>::as_ref(file)).unwrap(),
        ),
    );

    if let Some(expected) = expected {
        let output = output.bytes().unwrap();
        assert_eq!(output.as_slice(), expected);
    }
}

#[test]
fn builtins() {
    test_file("src/tests/builtins.pl", Some(b""));
}

#[test]
fn call_with_inference_limit() {
    test_file("src/tests/call_with_inference_limit.pl", Some(b""));
}

#[test]
fn facts() {
    test_file("src/tests/facts.pl", Some(b""));
}

#[test]
fn hello_world() {
    test_file(
        "src/tests/hello_world.pl",
        Some("Hello World!\n".as_bytes()),
    );
}

#[test]
fn predicates() {
    test_file("src/tests/predicates.pl", Some(b""));
}

#[test]
fn rules() {
    test_file("src/tests/rules.pl", Some(b""));
}

#[test]
#[ignore] // ignored as this does not appear to terminate
fn setup_call_cleanup() {
    test_file("src/tests/setup_call_cleanup.pl", Some(b""));
}

#[test]
fn clpz() {
    test_file("src/tests/clpz/test_clpz.pl", Some(b""));
}
