use crate::atom_table::*;
use crate::parser::ast::*;
use crate::parser::lexer::{Lexer, Token};

fn read_all_tokens(text: &str) -> Result<Vec<Token>, ParserError> {
    let mut machine_st = MachineState::new();
    let stream = parsing_stream(text.as_bytes())?;
    let mut lexer = Lexer::new(stream, &mut machine_st);

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
    assert_eq!(tokens, [Token::Literal(Literal::Fixnum(Fixnum::build_with(4)))]);
    Ok(())
}

#[test]
fn any_char_multiline_comment() -> Result<(), ParserError> {
    let tokens = read_all_tokens("/* █╗╚═══╝ © */ 4\n")?;
    assert_eq!(tokens, [Token::Literal(Literal::Fixnum(4))]);
    Ok(())
}

#[test]
fn simple_char() -> Result<(), ParserError> {
    let tokens = read_all_tokens("'a'\n")?;
    assert_eq!(tokens, [Token::Literal(Literal::Char('a'))]);
    Ok(())
}

#[test]
fn char_with_meta_seq() -> Result<(), ParserError> {
    let tokens = read_all_tokens(r#"'\\' '\'' '\"' '\`' "#)?; // use literal string so \ are escaped
    assert_eq!(
        tokens,
        [
            Token::Literal(Literal::Char('\\')),
            Token::Literal(Literal::Char('\'')),
            Token::Literal(Literal::Char('"')),
            Token::Literal(Literal::Char('`'))
        ]
    );
    Ok(())
}

#[test]
fn char_with_control_seq() -> Result<(), ParserError> {
    let tokens = read_all_tokens(r"'\a' '\b' '\r' '\f' '\t' '\n' '\v' ")?;
    assert_eq!(
        tokens,
        [
            Token::Literal(Literal::Char('\u{07}')),
            Token::Literal(Literal::Char('\u{08}')),
            Token::Literal(Literal::Char('\r')),
            Token::Literal(Literal::Char('\u{0c}')),
            Token::Literal(Literal::Char('\t')),
            Token::Literal(Literal::Char('\n')),
            Token::Literal(Literal::Char('\u{0b}')),
        ]
    );
    Ok(())
}

#[test]
fn char_with_octseq() -> Result<(), ParserError> {
    let tokens = read_all_tokens(r"'\60433\' ")?;
    assert_eq!(tokens, [Token::Literal(Literal::Char('愛'))]); // Japanese character
    Ok(())
}

#[test]
fn char_with_octseq_0() -> Result<(), ParserError> {
    let tokens = read_all_tokens(r"'\0\' ")?;
    assert_eq!(tokens, [Token::Literal(Literal::Char('\u{0000}'))]);
    Ok(())
}

#[test]
fn char_with_hexseq() -> Result<(), ParserError> {
    let tokens = read_all_tokens(r"'\x2124\' ")?;
    assert_eq!(tokens, [Token::Literal(Literal::Char('ℤ'))]); // Z math symbol
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
    assert!(read_all_tokens("% only a comment").is_err());
    Ok(())
}
