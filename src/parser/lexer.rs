use lexical::parse_lossy;

use crate::arena::ArenaAllocated;
use crate::atom_table::*;
pub use crate::machine::machine_state::*;
use crate::parser::ast::*;
use crate::parser::char_reader::*;
use crate::parser::dashu::Integer;

use std::convert::TryFrom;
use std::fmt;

macro_rules! consume_chars_with {
    ($token:expr, $e:expr) => {
        loop {
            match $e {
                Ok(Some(c)) => $token.push(c),
                Ok(None) => continue,
                Err($crate::parser::ast::ParserError::UnexpectedChar(..)) => break,
                Err(e) => return Err(e),
            }
        }
    };
}

#[derive(Debug, Default)]
struct LayoutInfo {
    inserted: bool,
    more: bool,
}

#[derive(Debug, PartialEq)]
pub enum Token {
    Literal(Literal),
    Var(String),
    Open,              // '('
    OpenCT,            // '('
    Close,             // ')'
    OpenList,          // '['
    CloseList,         // ']'
    OpenCurly,         // '{'
    CloseCurly,        // '}'
    HeadTailSeparator, // '|'
    Comma,             // ','
    End,
}

impl Token {
    #[inline]
    pub(super) fn is_end(&self) -> bool {
        if let Token::End = self {
            true
        } else {
            false
        }
    }
}

pub struct Lexer<'a, R> {
    pub(crate) reader: R,
    pub(crate) machine_st: &'a mut MachineState,
    pub(crate) line_num: usize,
    pub(crate) col_num: usize,
}

impl<'a, R: fmt::Debug> fmt::Debug for Lexer<'a, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Lexer")
            .field("reader", &"&'a mut R") // Hacky solution.
            .field("line_num", &self.line_num)
            .field("col_num", &self.col_num)
            .finish()
    }
}

impl<'a, R: CharRead> Lexer<'a, R> {
    pub fn new(src: R, machine_st: &'a mut MachineState) -> Self {
        Lexer {
            reader: src,
            machine_st,
            line_num: 0,
            col_num: 0,
        }
    }

    pub fn lookahead_char(&mut self) -> Result<char, ParserError> {
        match self.reader.peek_char() {
            Some(Ok(c)) => Ok(c),
            _ => Err(ParserError::unexpected_eof())
        }
    }

    pub fn read_char(&mut self) -> Result<char, ParserError> {
        match self.reader.read_char() {
            Some(Ok(c)) => Ok(c),
            _ => Err(ParserError::unexpected_eof())
        }
    }

    #[inline(always)]
    fn return_char(&mut self, c: char) {
        self.reader.put_back_char(c);
    }

    pub fn skip_char(&mut self, c: char) {
        self.reader.consume(c.len_utf8());

        if new_line_char!(c) {
            self.line_num += 1;
            self.col_num = 0;
        } else {
            self.col_num += 1;
        }
    }

    fn single_line_comment(&mut self) -> Result<(), ParserError> {
        loop {
            if self.reader.peek_char().is_none() {
                break;
            }

            let c = self.lookahead_char()?;
            self.skip_char(c);

            if new_line_char!(c) {
                break;
            }
        }

        Ok(())
    }

    fn bracketed_comment(&mut self) -> Result<bool, ParserError> {
        // we have already checked that the current lookahead_char is
        // comment_1_char, just skip it
        self.skip_char('/');

        let c = self.lookahead_char()?;

        if comment_2_char!(c) {
            self.skip_char(c);

            // Keep reading until we find characters '*' and '/'
            // Deliberately skip checks for prolog_char to allow
            // comments to contain any characters, including so-called
            // "extended characters", without having to explicitly add
            // them to a character class.

            let mut c = self.lookahead_char()?;

            let mut comment_loop = || -> Result<(), ParserError> {
                loop {
                    while !comment_2_char!(c) {
                        self.skip_char(c);
                        c = self.lookahead_char()?;
                    }

                    self.skip_char(c);
                    c = self.lookahead_char()?;

                    if comment_1_char!(c) {
                        break;
                    }
                }

                Ok(())
            };

            match comment_loop() {
                Err(e) if e.is_unexpected_eof() => {
                    return Err(ParserError::IncompleteReduction(self.line_num, self.col_num));
                }
                Err(e) => {
                    return Err(e);
                }
                Ok(_) => {
                }
            }

            if prolog_char!(c) {
                self.skip_char(c);
                Ok(true)
            } else {
                Err(ParserError::NonPrologChar(self.line_num, self.col_num))
            }
        } else {
            self.return_char('/');
            Ok(false)
        }
    }

    fn get_back_quoted_char(&mut self) -> Result<char, ParserError> {
        let c = self.lookahead_char()?;

        if back_quote_char!(c) {
            self.skip_char(c);
            let c2 = self.lookahead_char()?;

            if !back_quote_char!(c2) {
                self.return_char(c);
                Err(ParserError::UnexpectedChar(c, self.line_num, self.col_num))
            } else {
                self.skip_char(c2);
                Ok(c2)
            }
        } else if single_quote_char!(c) {
            self.skip_char(c);
            self.read_char()
        } else {
            self.get_non_quote_char()
        }
    }

    fn get_back_quoted_item(&mut self) -> Result<Option<char>, ParserError> {
        let c = self.lookahead_char()?;

        if backslash_char!(c) {
            self.skip_char(c);
            let c2 = self.lookahead_char()?;

            if new_line_char!(c2) {
                self.skip_char(c2);
                Ok(None)
            } else {
                self.return_char(c);
                Err(ParserError::UnexpectedChar(c, self.line_num, self.col_num))
            }
        } else {
            self.get_back_quoted_char().map(Some)
        }
    }

    fn get_back_quoted_string(&mut self) -> Result<String, ParserError> {
        let c = self.lookahead_char()?;

        if back_quote_char!(c) {
            self.skip_char(c);

            let mut token = String::with_capacity(16);
            consume_chars_with!(token, self.get_back_quoted_item());

            let c = self.lookahead_char()?;

            if back_quote_char!(c) {
                self.skip_char(c);
                Ok(token)
            } else {
                Err(ParserError::MissingQuote(self.line_num, self.col_num))
            }
        } else {
            Err(ParserError::UnexpectedChar(c, self.line_num, self.col_num))
        }
    }

    fn get_single_quoted_item(&mut self) -> Result<Option<char>, ParserError> {
        let c = self.lookahead_char()?;

        if backslash_char!(c) {
            self.skip_char(c);
            let c2 = self.lookahead_char()?;

            if new_line_char!(c2) {
                self.skip_char(c2);
                return Ok(None);
            } else {
                self.return_char(c);
            }
        }

        self.get_single_quoted_char().map(Some)
    }

    fn get_single_quoted_char(&mut self) -> Result<char, ParserError> {
        let c = self.lookahead_char()?;

        if single_quote_char!(c) {
            self.skip_char(c);
            let c2 = self.lookahead_char()?;

            if !single_quote_char!(c2) {
                self.return_char(c);
                Err(ParserError::UnexpectedChar(c, self.line_num, self.col_num))
            } else {
                self.skip_char(c2);
                Ok(c2)
            }
        } else if double_quote_char!(c) || back_quote_char!(c) {
            self.skip_char(c);
            Ok(c)
        } else {
            self.get_non_quote_char()
        }
    }

    fn get_double_quoted_item(&mut self) -> Result<Option<char>, ParserError> {
        let c = self.lookahead_char()?;

        if backslash_char!(c) {
            self.skip_char(c);

            let c2 = self.lookahead_char()?;

            if new_line_char!(c2) {
                self.skip_char(c2);
                return Ok(None);
            } else {
                self.return_char(c);
            }
        }

        self.get_double_quoted_char().map(Some)
    }

    fn get_double_quoted_char(&mut self) -> Result<char, ParserError> {
        let c = self.lookahead_char()?;

        if double_quote_char!(c) {
            self.skip_char(c);
            let c2 = self.lookahead_char()?;

            if !double_quote_char!(c2) {
                self.return_char(c);
                Err(ParserError::UnexpectedChar(c, self.line_num, self.col_num))
            } else {
                self.skip_char(c2);
                Ok(c2)
            }
        } else if single_quote_char!(c) || back_quote_char!(c) {
            self.skip_char(c);
            Ok(c)
        } else {
            self.get_non_quote_char()
        }
    }

    fn get_control_escape_sequence(&mut self) -> Result<char, ParserError> {
        let c = self.lookahead_char()?;

        let escaped = match c {
            'a' => '\u{07}', // UTF-8 alert
            'b' => '\u{08}', // UTF-8 backspace
            'v' => '\u{0b}', // UTF-8 vertical tab
            'f' => '\u{0c}', // UTF-8 form feed
            't' => '\t',
            'n' => '\n',
            'r' => '\r',
            c => return Err(ParserError::UnexpectedChar(c, self.line_num, self.col_num)),
        };

        self.skip_char(c);
        Ok(escaped)
    }

    fn get_octal_escape_sequence(&mut self) -> Result<char, ParserError> {
        self.escape_sequence_to_char(|c| octal_digit_char!(c), 8)
    }

    fn get_hexadecimal_escape_sequence(&mut self, start: char) -> Result<char, ParserError> {
        self.skip_char(start);
        let c = self.lookahead_char()?;

        if hexadecimal_digit_char!(c) {
            self.escape_sequence_to_char(|c| hexadecimal_digit_char!(c), 16)
        } else {
            Err(ParserError::IncompleteReduction(self.line_num, self.col_num))
        }
    }

    fn escape_sequence_to_char(
        &mut self,
        accept_char: impl Fn(char) -> bool,
        radix: u32,
    ) -> Result<char, ParserError> {
        let mut c = self.lookahead_char()?;
        let mut token = String::with_capacity(16);

        loop {
            token.push(c);

            self.skip_char(c);
            c = self.lookahead_char()?;

            if !accept_char(c) {
                break;
            }
        }

        if backslash_char!(c) {
            self.skip_char(c);
            u32::from_str_radix(&token, radix).map_or_else(
                |_| Err(ParserError::ParseBigInt(self.line_num, self.col_num)),
                |n| {
                    char::try_from(n)
                        .map_err(|_| ParserError::Utf8Error(self.line_num, self.col_num))
                },
            )
        } else {
            Err(ParserError::IncompleteReduction(self.line_num, self.col_num))
        }
    }

    fn get_non_quote_char(&mut self) -> Result<char, ParserError> {
        let c = self.lookahead_char()?;

        if graphic_char!(c) || alpha_numeric_char!(c) || solo_char!(c) || space_char!(c) {
            self.skip_char(c);
            Ok(c)
        } else {
            if !backslash_char!(c) {
                return Err(ParserError::UnexpectedChar(c, self.line_num, self.col_num));
            }

            self.skip_char(c);
            let c = self.lookahead_char()?;

            if meta_char!(c) {
                self.skip_char(c);
                Ok(c)
            } else if octal_digit_char!(c) {
                self.get_octal_escape_sequence()
            } else if symbolic_hexadecimal_char!(c) {
                self.get_hexadecimal_escape_sequence(c)
            } else {
                self.get_control_escape_sequence()
            }
        }
    }

    fn char_code_list_token(&mut self, start: char) -> Result<String, ParserError> {
        let mut token = String::with_capacity(16);

        self.skip_char(start);
        consume_chars_with!(token, self.get_double_quoted_item());

        let c = self.lookahead_char()?;

        if double_quote_char!(c) {
            self.skip_char(c);
            Ok(token)
        } else {
            Err(ParserError::MissingQuote(self.line_num, self.col_num))
        }
    }

    fn hexadecimal_constant(&mut self, start: char) -> Result<Token, ParserError> {
        self.skip_char(start);
        let mut c = self.lookahead_char()?;

        if hexadecimal_digit_char!(c) {
            let mut token = String::with_capacity(16);

            loop {
                if hexadecimal_digit_char!(c) {
                    self.skip_char(c);
                    token.push(c);
                    c = self.lookahead_char()?;
                } else {
                    break;
                }
            }

            i64::from_str_radix(&token, 16)
                .map(|n| Token::Literal(fixnum!(Literal, n, &mut self.machine_st.arena)))
                .or_else(|_| {
                    Integer::from_str_radix(&token, 16)
                        .map(|n| Token::Literal(Literal::Integer(
                            arena_alloc!(n, &mut self.machine_st.arena)
                        )))
                        .map_err(|_| ParserError::ParseBigInt(self.line_num, self.col_num))
                })
        } else {
            self.return_char(start);
            Err(ParserError::ParseBigInt(self.line_num, self.col_num))
        }
    }

    fn octal_constant(&mut self, start: char) -> Result<Token, ParserError> {
        self.skip_char(start);
        let mut c = self.lookahead_char()?;

        if octal_digit_char!(c) {
            let mut token = String::with_capacity(16);

            loop {
                if octal_digit_char!(c) {
                    self.skip_char(c);
                    token.push(c);
                    c = self.lookahead_char()?;
                } else {
                    break;
                }
            }

            i64::from_str_radix(&token, 8)
                .map(|n| Token::Literal(fixnum!(Literal, n, &mut self.machine_st.arena)))
                .or_else(|_| {
                    Integer::from_str_radix(&token, 8)
                        .map(|n| Token::Literal(Literal::Integer(
                            arena_alloc!(n, &mut self.machine_st.arena)
                        )))
                        .map_err(|_| ParserError::ParseBigInt(self.line_num, self.col_num))
                })
        } else {
            self.return_char(start);
            Err(ParserError::ParseBigInt(self.line_num, self.col_num))
        }
    }

    fn binary_constant(&mut self, start: char) -> Result<Token, ParserError> {
        self.skip_char(start);
        let mut c = self.lookahead_char()?;

        if binary_digit_char!(c) {
            let mut token = String::with_capacity(16);

            loop {
                if binary_digit_char!(c) {
                    self.skip_char(c);
                    token.push(c);
                    c = self.lookahead_char()?;
                } else {
                    break;
                }
            }

            i64::from_str_radix(&token, 2)
                .map(|n| Token::Literal(fixnum!(Literal, n, &mut self.machine_st.arena)))
                .or_else(|_| {
                    Integer::from_str_radix(&token, 2)
                        .map(|n| Token::Literal(Literal::Integer(
                            arena_alloc!(n, &mut self.machine_st.arena)
                        )))
                        .map_err(|_| ParserError::ParseBigInt(self.line_num, self.col_num))
                })
        } else {
            self.return_char(start);
            Err(ParserError::ParseBigInt(self.line_num, self.col_num))
        }
    }

    fn variable_token(&mut self) -> Result<Token, ParserError> {
        let mut s = String::with_capacity(16);
        s.push(self.read_char()?);

        loop {
            let c = self.lookahead_char()?;

            if alpha_numeric_char!(c) {
                self.skip_char(c);
                s.push(c);
            } else {
                break;
            }
        }

        Ok(Token::Var(s))
    }

    fn name_token(&mut self, c: char) -> Result<Token, ParserError> {
        let mut token = String::with_capacity(16);

        if small_letter_char!(c) {
            self.skip_char(c);
            token.push(c);

            loop {
                let c = self.lookahead_char()?;

                if alpha_numeric_char!(c) {
                    self.skip_char(c);
                    token.push(c);
                } else {
                    break;
                }
            }
        } else if graphic_token_char!(c) {
            self.skip_char(c);
            token.push(c);

            loop {
                let c = self.lookahead_char()?;

                if graphic_token_char!(c) {
                    self.skip_char(c);
                    token.push(c);
                } else {
                    break;
                }
            }
        } else if cut_char!(c) {
            self.skip_char(c);
            token.push(c);
        } else if semicolon_char!(c) {
            self.skip_char(c);
            token.push(c);
        } else if single_quote_char!(c) {
            self.skip_char(c);
            consume_chars_with!(token, self.get_single_quoted_item());

            let c = self.lookahead_char()?;

            if single_quote_char!(c) {
                self.skip_char(c);

                if !token.is_empty() && token.chars().nth(1).is_none() {
                    if let Some(c) = token.chars().next() {
                        return Ok(Token::Literal(Literal::Char(c)));
                    }
                }
            } else {
                return Err(ParserError::InvalidSingleQuotedCharacter(c));
            }
        } else {
            match self.get_back_quoted_string() {
                Ok(_) => return Err(ParserError::BackQuotedString(self.line_num, self.col_num)),
                Err(e) => return Err(e),
            }
        }

        if token.as_str() == "[]" {
            Ok(Token::Literal(Literal::Atom(atom!("[]"))))
        } else {
            Ok(Token::Literal(Literal::Atom(
                self.machine_st.atom_tbl.build_with(&token),
            )))
        }
    }

    fn vacate_with_float(&mut self, mut token: String) -> Result<Token, ParserError> {
        self.return_char(token.pop().unwrap());
        let n = parse_lossy::<f64, _>(token.as_bytes())?;
        Ok(Token::Literal(Literal::from(float_alloc!(n, self.machine_st.arena))))
    }

    fn skip_underscore_in_number(&mut self) -> Result<char, ParserError> {
        let mut c = self.lookahead_char()?;

        if c == '_' {
            self.skip_char(c);
            self.scan_for_layout()?;
            c = self.lookahead_char()?;

            if decimal_digit_char!(c) {
                Ok(c)
            } else {
                Err(ParserError::ParseBigInt(self.line_num, self.col_num))
            }
        } else {
            Ok(c)
        }
    }

    pub fn number_token(&mut self, leading_c: char) -> Result<Token, ParserError> {
        let mut token = String::with_capacity(16);

        self.skip_char(leading_c);
        token.push(leading_c);
        let mut c = self.skip_underscore_in_number()?;

        while decimal_digit_char!(c) {
            token.push(c);
            self.skip_char(c);
            c = self.skip_underscore_in_number()?;
        }

        if decimal_point_char!(c) {
            self.skip_char(c);

            if self.reader.peek_char().is_none() {
                self.return_char('.');

                i64::from_str_radix(&token, 10)
                    .map(|n| Token::Literal(fixnum!(Literal, n, &mut self.machine_st.arena)))
                    .or_else(|_| {
                        token
                            .parse::<Integer>()
                            .map(|n| {
                                Token::Literal(Literal::Integer(arena_alloc!(n, &mut self.machine_st.arena)))
                            })
                            .map_err(|_| ParserError::ParseBigInt(self.line_num, self.col_num))
                    })
            } else if decimal_digit_char!(self.lookahead_char()?) {
                token.push('.');
                token.push(self.read_char()?);

                let mut c = self.lookahead_char()?;

                while decimal_digit_char!(c) {
                    token.push(c);
                    self.skip_char(c);
                    c = self.lookahead_char()?;
                }

                if exponent_char!(c) {
                    self.skip_char(c);
                    token.push(c);

                    let c = match self.lookahead_char() {
                        Err(_) => return Ok(self.vacate_with_float(token)?),
                        Ok(c) => c,
                    };

                    if !sign_char!(c) && !decimal_digit_char!(c) {
                        return Ok(self.vacate_with_float(token)?);
                    }

                    if sign_char!(c) {
                        self.skip_char(c);
                        token.push(c);

                        let c = match self.lookahead_char() {
                            Err(_) => {
                                self.return_char(token.pop().unwrap());
                                return Ok(self.vacate_with_float(token)?);
                            }
                            Ok(c) => c,
                        };

                        if !decimal_digit_char!(c) {
                            self.return_char(token.pop().unwrap());
                            return Ok(self.vacate_with_float(token)?);
                        }
                    }

                    let mut c = self.lookahead_char()?;

                    if decimal_digit_char!(c) {
                        self.skip_char(c);
                        token.push(c);

                        loop {
                            c = self.lookahead_char()?;

                            if decimal_digit_char!(c) {
                                self.skip_char(c);
                                token.push(c);
                            } else {
                                break;
                            }
                        }

                        let n = parse_lossy::<f64, _>(token.as_bytes())?;
                        Ok(Token::Literal(Literal::from(
                            float_alloc!(n, self.machine_st.arena)
                        )))
                    } else {
                        return Ok(self.vacate_with_float(token)?);
                    }
                } else {
                    let n = parse_lossy::<f64, _>(token.as_bytes())?;
                    Ok(Token::Literal(Literal::from(
                        float_alloc!(n, self.machine_st.arena)
                    )))
                }
            } else {
                self.return_char('.');

                i64::from_str_radix(&token, 10)
                    .map(|n| Token::Literal(fixnum!(Literal, n, &mut self.machine_st.arena)))
                    .or_else(|_| {
                        token
                            .parse::<Integer>()
                            .map(|n| {
                                Token::Literal(Literal::Integer(arena_alloc!(n, &mut self.machine_st.arena)))
                            })
                            .map_err(|_| ParserError::ParseBigInt(self.line_num, self.col_num))
                    })
            }
        } else {
            if token.starts_with('0') && token.len() == 1 {
                if c == 'x' {
                    self.hexadecimal_constant(c).or_else(|e| {
                        if let ParserError::ParseBigInt(..) = e {
                            i64::from_str_radix(&token, 10)
                                .map(|n| Token::Literal(fixnum!(Literal, n, &mut self.machine_st.arena)))
                                .or_else(|_| {
                                    token
                                        .parse::<Integer>()
                                        .map(|n| {
                                            Token::Literal(Literal::Integer(arena_alloc!(
                                                n,
                                                &mut self.machine_st.arena
                                            )))
                                        })
                                        .map_err(|_| {
                                            ParserError::ParseBigInt(self.line_num, self.col_num)
                                        })
                                })
                        } else {
                            Err(e)
                        }
                    })
                } else if c == 'o' {
                    self.octal_constant(c).or_else(|e| {
                        if let ParserError::ParseBigInt(..) = e {
                            i64::from_str_radix(&token, 10)
                                .map(|n| Token::Literal(fixnum!(Literal, n, &mut self.machine_st.arena)))
                                .or_else(|_| {
                                    token
                                        .parse::<Integer>()
                                        .map(|n| {
                                            Token::Literal(Literal::Integer(arena_alloc!(
                                                n,
                                                &mut self.machine_st.arena
                                            )))
                                        })
                                        .map_err(|_| {
                                            ParserError::ParseBigInt(self.line_num, self.col_num)
                                        })
                                })
                        } else {
                            Err(e)
                        }
                    })
                } else if c == 'b' {
                    self.binary_constant(c).or_else(|e| {
                        if let ParserError::ParseBigInt(..) = e {
                            i64::from_str_radix(&token, 10)
                                .map(|n| Token::Literal(fixnum!(Literal, n, &mut self.machine_st.arena)))
                                .or_else(|_| {
                                    token
                                        .parse::<Integer>()
                                        .map(|n| {
                                            Token::Literal(Literal::Integer(arena_alloc!(
                                                n,
                                                &mut self.machine_st.arena
                                            )))
                                        })
                                        .map_err(|_| {
                                            ParserError::ParseBigInt(self.line_num, self.col_num)
                                        })
                                })
                        } else {
                            Err(e)
                        }
                    })
                } else if single_quote_char!(c) {
                    self.skip_char(c);
                    let c = self.lookahead_char()?;

                    if backslash_char!(c) {
                        self.skip_char(c);
                        let c = self.lookahead_char()?;

                        if new_line_char!(c) {
                            self.skip_char(c);
                            self.return_char('\'');

                            return Ok(Token::Literal(Literal::Fixnum(Fixnum::build_with(0))));
                        } else {
                            self.return_char('\\');
                        }
                    }

                    self.get_single_quoted_char()
                        .map(|c| Token::Literal(Literal::Fixnum(Fixnum::build_with(c as i64))))
                        .or_else(|err| {
                            match err {
                                ParserError::UnexpectedChar('\'', ..) => {
                                }
                                err => return Err(err),
                            }

                            self.return_char(c);

                            i64::from_str_radix(&token, 10)
                                .map(|n| Token::Literal(fixnum!(Literal, n, &mut self.machine_st.arena)))
                                .or_else(|_| {
                                    token
                                        .parse::<Integer>()
                                        .map(|n| {
                                            Token::Literal(Literal::Integer(arena_alloc!(
                                                n,
                                                &mut self.machine_st.arena
                                            )))
                                        })
                                        .map_err(|_| {
                                            ParserError::ParseBigInt(self.line_num, self.col_num)
                                        })
                                })
                        })
                } else {
                    i64::from_str_radix(&token, 10)
                        .map(|n| Token::Literal(fixnum!(Literal, n, &mut self.machine_st.arena)))
                        .or_else(|_| {
                            token
                                .parse::<Integer>()
                                .map(|n| {
                                    Token::Literal(Literal::Integer(arena_alloc!(
                                        n,
                                        &mut self.machine_st.arena
                                    )))
                                })
                                .map_err(|_| ParserError::ParseBigInt(self.line_num, self.col_num))
                        })
                }
            } else {
                i64::from_str_radix(&token, 10)
                    .map(|n| Token::Literal(fixnum!(Literal, n, &mut self.machine_st.arena)))
                    .or_else(|_| {
                        token
                            .parse::<Integer>()
                            .map(|n| {
                                Token::Literal(Literal::Integer(arena_alloc!(n, &mut self.machine_st.arena)))
                            })
                            .map_err(|_| ParserError::ParseBigInt(self.line_num, self.col_num))
                    })
            }
        }
    }

    fn consume_layout(
        &mut self,
        c: Option<char>,
        layout_info: &mut LayoutInfo,
    ) -> Result<(), ParserError> {
        match c {
            Some(c) if layout_char!(c) => {
                self.skip_char(c);
                layout_info.inserted = true;
            }
            Some(c) if end_line_comment_char!(c) => {
                self.single_line_comment()?;
                layout_info.inserted = true;
            }
            Some(c) if comment_1_char!(c) => {
                if self.bracketed_comment()? {
                    layout_info.inserted = true;
                } else {
                    layout_info.more = false;
                }
            }
            _ => {
                layout_info.more = false;
            }
        }

        Ok(())
    }

    pub fn scan_for_layout(&mut self) -> Result<bool, ParserError> {
        match self.lookahead_char() {
            Err(e) => {
                Err(e)
            }
            Ok(c) => {
                let mut layout_info = LayoutInfo { inserted: false, more: true };
                let mut cr = Some(c);

                loop {
                    self.consume_layout(cr, &mut layout_info)?;

                    if !layout_info.more {
                        break;
                    }

                    cr = self.lookahead_char().ok();
                }

                Ok(layout_info.inserted)
            }
        }
    }

    pub fn next_token(&mut self) -> Result<Token, ParserError> {
        let layout_inserted = self.scan_for_layout()?;
        let cr = self.lookahead_char();

        match cr {
            Ok(c) => {
                if capital_letter_char!(c) || variable_indicator_char!(c) {
                    return self.variable_token();
                }

                if c == ',' {
                    self.skip_char(c);
                    return Ok(Token::Comma);
                }

                if c == ')' {
                    self.skip_char(c);
                    return Ok(Token::Close);
                }

                if c == '(' {
                    self.skip_char(c);
                    return Ok(if layout_inserted {
                        Token::Open
                    } else {
                        Token::OpenCT
                    });
                }

                if c == '.' {
                    self.skip_char(c);

                    match self.lookahead_char() {
                        Ok(c) if layout_char!(c) || c == '%' => {
                            if new_line_char!(c) {
                                self.skip_char(c);
                            }

                            return Ok(Token::End);
                        }
                        Err(e) if e.is_unexpected_eof() => {
                            return Ok(Token::End);
                        }
                        _ => {
                            self.return_char('.');
                        }
                    };

                    return self.name_token(c);
                }

                if decimal_digit_char!(c) {
                    return self.number_token(c);
                }

                if c == ']' {
                    self.skip_char(c);
                    return Ok(Token::CloseList);
                }

                if c == '[' {
                    self.skip_char(c);
                    return Ok(Token::OpenList);
                }

                if c == '|' {
                    self.skip_char(c);
                    return Ok(Token::HeadTailSeparator);
                }

                if c == '{' {
                    self.skip_char(c);
                    return Ok(Token::OpenCurly);
                }

                if c == '}' {
                    self.skip_char(c);
                    return Ok(Token::CloseCurly);
                }

                if c == '"' {
                    let s = self.char_code_list_token(c)?;
                    let atom = self.machine_st.atom_tbl.build_with(&s);

                    return if let DoubleQuotes::Atom = self.machine_st.flags.double_quotes {
                        Ok(Token::Literal(Literal::Atom(atom)))
                    } else {
                        Ok(Token::Literal(Literal::String(atom)))
                    };
                }

                if c == '\u{0}' {
                    return Err(ParserError::unexpected_eof())
                }

                self.name_token(c)
            }
            Err(e) => Err(e),
        }
    }
}
