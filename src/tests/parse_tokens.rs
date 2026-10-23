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

#[test]
fn decimal_with_underscore() -> Result<(), ParserError> {
    let tokens = read_all_tokens("1_000")?;
    assert_eq!(tokens, [Token::Literal(Literal::Fixnum(Fixnum::build_with(1000)))]);
    Ok(())
}

#[test]
fn decimal_with_multiple_underscores() -> Result<(), ParserError> {
    let tokens = read_all_tokens("1_000_000")?;
    assert_eq!(tokens, [Token::Literal(Literal::Fixnum(Fixnum::build_with(1000000)))]);
    Ok(())
}

#[test]
fn decimal_with_underscore_and_whitespace() -> Result<(), ParserError> {
    let tokens = read_all_tokens("123_ 456")?;
    assert_eq!(tokens, [Token::Literal(Literal::Fixnum(Fixnum::build_with(123456)))]);
    Ok(())
}

#[test]
fn decimal_with_underscore_and_comment() -> Result<(), ParserError> {
    let tokens = read_all_tokens("123_ /* comment */ 456")?;
    assert_eq!(tokens, [Token::Literal(Literal::Fixnum(Fixnum::build_with(123456)))]);
    Ok(())
}

#[test]
fn hexadecimal_with_underscore() -> Result<(), ParserError> {
    let tokens = read_all_tokens("0xDE_AD")?;
    assert_eq!(tokens, [Token::Literal(Literal::Fixnum(Fixnum::build_with(0xDEAD)))]);
    Ok(())
}

#[test]
fn hexadecimal_with_multiple_underscores() -> Result<(), ParserError> {
    let tokens = read_all_tokens("0x1_2_3_4")?;
    assert_eq!(tokens, [Token::Literal(Literal::Fixnum(Fixnum::build_with(0x1234)))]);
    Ok(())
}

#[test]
fn hexadecimal_with_underscore_and_whitespace() -> Result<(), ParserError> {
    let tokens = read_all_tokens("0xFF_ 00")?;
    assert_eq!(tokens, [Token::Literal(Literal::Fixnum(Fixnum::build_with(0xFF00)))]);
    Ok(())
}

#[test]
fn hexadecimal_with_underscore_and_comment() -> Result<(), ParserError> {
    let tokens = read_all_tokens("0xDE_ /* test */ AD")?;
    assert_eq!(tokens, [Token::Literal(Literal::Fixnum(Fixnum::build_with(0xDEAD)))]);
    Ok(())
}

#[test]
fn octal_with_underscore() -> Result<(), ParserError> {
    let tokens = read_all_tokens("0o7_6")?;
    assert_eq!(tokens, [Token::Literal(Literal::Fixnum(Fixnum::build_with(0o76)))]);
    Ok(())
}

#[test]
fn octal_with_multiple_underscores() -> Result<(), ParserError> {
    let tokens = read_all_tokens("0o1_2_3")?;
    assert_eq!(tokens, [Token::Literal(Literal::Fixnum(Fixnum::build_with(0o123)))]);
    Ok(())
}

#[test]
fn octal_with_underscore_and_whitespace() -> Result<(), ParserError> {
    let tokens = read_all_tokens("0o77_ 00")?;
    assert_eq!(tokens, [Token::Literal(Literal::Fixnum(Fixnum::build_with(0o7700)))]);
    Ok(())
}

#[test]
fn octal_with_underscore_and_comment() -> Result<(), ParserError> {
    let tokens = read_all_tokens("0o1_ /* octal */ 23")?;
    assert_eq!(tokens, [Token::Literal(Literal::Fixnum(Fixnum::build_with(0o123)))]);
    Ok(())
}

#[test]
fn binary_with_underscore() -> Result<(), ParserError> {
    let tokens = read_all_tokens("0b10_11")?;
    assert_eq!(tokens, [Token::Literal(Literal::Fixnum(Fixnum::build_with(0b1011)))]);
    Ok(())
}

#[test]
fn binary_with_multiple_underscores() -> Result<(), ParserError> {
    let tokens = read_all_tokens("0b1_0_1_0")?;
    assert_eq!(tokens, [Token::Literal(Literal::Fixnum(Fixnum::build_with(0b1010)))]);
    Ok(())
}

#[test]
fn binary_with_underscore_and_whitespace() -> Result<(), ParserError> {
    let tokens = read_all_tokens("0b1111_ 0000")?;
    assert_eq!(tokens, [Token::Literal(Literal::Fixnum(Fixnum::build_with(0b11110000)))]);
    Ok(())
}

#[test]
fn binary_with_underscore_and_comment() -> Result<(), ParserError> {
    let tokens = read_all_tokens("0b10_ /* binary */ 11")?;
    assert_eq!(tokens, [Token::Literal(Literal::Fixnum(Fixnum::build_with(0b1011)))]);
    Ok(())
}
