use crate::atom_table::*;
use crate::parser::ast::*;
use crate::parser::lexer::{Lexer, Token};

#[test]
fn valid_token() {
    let stream = parsing_stream("valid text".as_bytes());
    assert!(stream.is_ok());
}

#[test]
fn empty_stream() {
    let bytes: &[u8] = &[];
    assert!(parsing_stream(bytes).is_ok());
}

#[test]
fn skip_utf8_bom() {
    let mut machine_st = MachineState::new();
    let bytes: &[u8] = &[0xEF, 0xBB, 0xBF, '4' as u8, '\n' as u8];
    let stream = parsing_stream(bytes).expect("valid stream");
    let mut lexer = Lexer::new(stream, &mut machine_st);
    match lexer.next_token() {
        Ok(Token::Literal(Literal::Fixnum(Fixnum::build_with(4)))) => (),
        _ => assert!(false),
    }
}

#[test]
fn invalid_utf16_bom() {
    let bytes: &[u8] = &[0xFF, 0xFE, 'a' as u8, '\n' as u8];
    let stream = parsing_stream(bytes);
    match stream {
        Err(ParserError::Utf8Error(0, 0)) => (),
        _ => assert!(false),
    }
}
