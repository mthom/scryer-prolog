extern crate prolog_parser;

use prolog_parser::ast::*;
use prolog_parser::lexer::{Lexer, Token};
use prolog_parser::tabled_rc::TabledData;

use std::rc::Rc;

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
    let atom_tbl = TabledData::new(Rc::new("my_module".to_string()));
    let flags = MachineFlags::default();
    let bytes: &[u8] = &[0xEF, 0xBB, 0xBF, '4' as u8, '\n' as u8];
    let mut stream = parsing_stream(bytes).expect("valid stream");
    let mut lexer = Lexer::new(atom_tbl, flags, &mut stream);
    match lexer.next_token() {
        Ok(Token::Constant(Constant::Fixnum(4))) => (),
        _ => assert!(false)
    }
}

#[test]
fn invalid_utf16_bom() {
    let bytes: &[u8] = &[0xFF, 0xFE, 'a' as u8, '\n' as u8];
    let stream = parsing_stream(bytes);
    match stream {
        Err(ParserError::Utf8Error(0, 0)) => (),
        _ => assert!(false)
    }
}

