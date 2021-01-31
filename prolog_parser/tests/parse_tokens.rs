extern crate prolog_parser;

use prolog_parser::ast::*;
use prolog_parser::lexer::{Lexer, Token};
use prolog_parser::tabled_rc::TabledData;

use std::rc::Rc;

fn read_all_tokens(text: &str) -> Result<Vec<Token>, ParserError> {
    let atom_tbl = TabledData::new(Rc::new("my_module".to_string()));
    let flags = MachineFlags::default();
    let mut stream = parsing_stream(text.as_bytes())?;
    let mut lexer = Lexer::new(atom_tbl, flags, &mut stream);

    let mut tokens = Vec::new();
    while !lexer.eof()? {
        let token = lexer.next_token()?;
        tokens.push(token);
    }
    Ok(tokens)
}

#[test]
fn empty_multiline_comment() -> Result<(), ParserError> {
    let tokens = read_all_tokens("/**/ 4\n")?;
    assert_eq!(tokens, [Token::Constant(Constant::Fixnum(4))]);
    Ok(())
}

#[test]
fn any_char_multiline_comment() -> Result<(), ParserError> {
    let tokens = read_all_tokens("/* █╗╚═══╝ © */ 4\n")?;
    assert_eq!(tokens, [Token::Constant(Constant::Fixnum(4))]);
    Ok(())
}

#[test]
fn simple_char() -> Result<(), ParserError> {
    let tokens = read_all_tokens("'a'\n")?;
    assert_eq!(tokens, [Token::Constant(Constant::Char('a'))]);
    Ok(())
}

#[test]
fn char_with_meta_seq() -> Result<(), ParserError> {
    let tokens = read_all_tokens(r#"'\\' '\'' '\"' '\`' "#)?; // use literal string so \ are escaped
    assert_eq!(tokens, [Token::Constant(Constant::Char('\\')),
    Token::Constant(Constant::Char('\'')),
    Token::Constant(Constant::Char('"')),
    Token::Constant(Constant::Char('`'))]);
    Ok(())
}

#[test]
fn char_with_control_seq() -> Result<(), ParserError> {
    let tokens = read_all_tokens(r"'\a' '\b' '\r' '\f' '\t' '\n' '\v' ")?;
    assert_eq!(tokens, [
        Token::Constant(Constant::Char('\u{07}')),
        Token::Constant(Constant::Char('\u{08}')),
        Token::Constant(Constant::Char('\r')),
        Token::Constant(Constant::Char('\u{0c}')),
        Token::Constant(Constant::Char('\t')),
        Token::Constant(Constant::Char('\n')),
        Token::Constant(Constant::Char('\u{0b}')),
    ]);
    Ok(())
}

#[test]
fn char_with_octseq() -> Result<(), ParserError> {
    let tokens = read_all_tokens(r"'\60433\' ")?;
    assert_eq!(tokens, [Token::Constant(Constant::Char('愛'))]); // Japanese character
    Ok(())
}

#[test]
fn char_with_octseq_0() -> Result<(), ParserError> {
    let tokens = read_all_tokens(r"'\0\' ")?;
    assert_eq!(tokens, [Token::Constant(Constant::Char('\u{0000}'))]);
    Ok(())
}

#[test]
fn char_with_hexseq() -> Result<(), ParserError> {
    let tokens = read_all_tokens(r"'\x2124\' ")?;
    assert_eq!(tokens, [Token::Constant(Constant::Char('ℤ'))]); // Z math symbol
    Ok(())
}

#[test]
fn char_with_hexseq_invalid() {
    assert!(read_all_tokens(r"'\x\' ").is_err());
}

#[test]
fn empty() -> Result<(), ParserError> {
    let tokens = read_all_tokens("")?;
    assert!(tokens.is_empty());
    Ok(())
}

#[test]
fn comment_then_eof() -> Result<(), ParserError> {
    let tokens = read_all_tokens("% only a comment")?;
    assert_eq!(tokens, [Token::End]);
    Ok(())
}
