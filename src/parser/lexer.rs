use crate::arena::opt_in_buf_reader::GraphemeRead;
use crate::atom_table::*;
pub use crate::machine::machine_state::*;
use crate::offset_table::*;
use crate::parser::ast::*;
use crate::parser::dashu::Integer;
use crate::parser::grapheme_classifiers::*;

use ordered_float::OrderedFloat;

use compact_str::*;

use std::convert::TryFrom;
use std::fmt;

macro_rules! consume_graphemes_with {
    ($token:expr, $e:expr) => {
        loop {
            match $e {
                Ok(Some(c)) => $token.push_str(c.as_ref()),
                Ok(None) => continue,
                Err($crate::parser::ast::ParserError {
                    kind: $crate::parser::ast::ParserErrorKind::UnexpectedGrapheme(..),
                    ..
                }) => break,
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

#[derive(Debug)]
pub enum Token {
    Literal(Literal),
    Var(CompactString),
    String(CompactString),
    Open,              // '('
    OpenCT,            // '('
    Close,             // ')'
    OpenList,          // '['
    CloseList,         // ']'
    OpenCurly,         // '{'
    CloseCurly,        // '}'
    HeadTailSeparator, // '|'
    DoubleBar,         // '||'
    Comma,             // ','
    End,
}

impl Token {
    #[inline]
    pub(super) fn is_end(&self) -> bool {
        matches!(self, Token::End)
    }
}

#[derive(Debug)]
enum NumberToken {
    Integer(GInteger),
    Float(F64Offset, OrderedFloat<f64>),
    Partial(CompactString),
}

impl NumberToken {
    #[inline]
    #[allow(clippy::wrong_self_convention)]
    fn to_token(self) -> Option<Token> {
        match self {
            NumberToken::Float(offset, fl) => Some(Token::Literal(Literal::F64(offset, fl))),
            NumberToken::Integer(GInteger::Integer(n)) => Some(Token::Literal(Literal::Integer(n))),
            NumberToken::Integer(GInteger::Fixnum(n)) => Some(Token::Literal(Literal::Fixnum(n))),
            NumberToken::Partial(_) => None,
        }
    }
}

macro_rules! try_nt {
    ($token:expr, $e: expr) => {{
        match $e {
            Ok(c) => c,
            Err(e) => {
                return if e.is_unexpected_eof() {
                    Ok(NumberToken::Partial($token))
                } else {
                    Err(e)
                };
            }
        }
    }};
}

pub(crate) struct Lexer<'a, R> {
    pub(crate) reader: R,
    pub(crate) machine_st: &'a mut MachineState,
    pub(crate) location: Location,
}

impl<'a, R: fmt::Debug> fmt::Debug for Lexer<'a, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("LexerParser")
            .field("reader", &"&'a mut R") // Hacky solution.
            .field("location", &self.location)
            .finish()
    }
}

impl<R> Lexer<'_, R> {
    pub(crate) fn located_error(&self, kind: ParserErrorKind) -> ParserError {
        ParserError {
            location: Some(self.location.clone()),
            kind,
        }
    }

    pub(crate) fn parse_big_int_error(&self) -> ParserError {
        self.located_error(ParserErrorKind::ParseBigInt)
    }

    pub(crate) fn incomplete_reduction(&self) -> ParserError {
        self.located_error(ParserErrorKind::IncompleteReduction)
    }

    pub(crate) fn unexpected_grapheme(&self, c: String) -> ParserError {
        self.located_error(ParserErrorKind::UnexpectedGrapheme(c))
    }
}

impl<'a, R: GraphemeRead> Lexer<'a, R> {
    pub fn new(reader: R, machine_st: &'a mut MachineState) -> Self {
        Self {
            reader,
            machine_st,
            location: Location::BOF,
        }
    }

    pub fn bad_utf8(&self) -> ParserError {
        self.located_error(ParserErrorKind::Utf8Error)
    }

    pub fn peek_grapheme(&mut self, at: usize) -> Result<&str, ParserError> {
        match self.reader.peek_grapheme(at) {
            Ok(Some(g)) => Ok(g),
            Ok(None) => Err(ParserError::unexpected_eof()),
            Err(e) => Err(ParserError::from(e)),
        }
    }

    fn skip_graphemes_up_to(&mut self, mut at: usize) -> Result<(), ParserError> {
        while at > 0 {
            let g = self.skip_grapheme()?;
            at = at.saturating_sub(g.len());
        }

        Ok(())
    }

    pub fn skip_grapheme(&mut self) -> Result<CompactString, ParserError> {
        // bstr's grapheme() routine, which GraphemeRead is built on,
        // emits "\u{FFFD}" to flag bad UTF-8. Only Scryer's lexer is
        // concerned with reporting these errors to the runtime, and
        // only does so once it has "committed" to a grapheme by
        // calling skip_grapheme. other consumers of Stream are
        // responsible for checking for bad UTF-8 via this codepoint
        // if desired.
        match self.reader.read_grapheme()? {
            Some(g) if g == "\u{FFFD}" => Err(self.bad_utf8()),
            Some(g) => {
                self.location.incr(g.as_str());
                Ok(g)
            }
            _ => Err(ParserError::unexpected_eof()),
        }
    }

    fn single_line_comment(&mut self) -> Result<(), ParserError> {
        loop {
            if self.skip_grapheme()? == "\n" {
                break;
            }
        }

        Ok(())
    }

    fn bracketed_comment(&mut self) -> Result<bool, ParserError> {
        // peek past the "/" to confirm "*"
        if self.peek_grapheme("/".len())? == "*" {
            self.skip_grapheme()?;
            self.skip_grapheme()?;

            // Keep reading until we find characters '*' and '/'
            // Deliberately skip checks for prolog_char to allow
            // comments to contain any characters, including so-called
            // "extended characters", without having to explicitly add
            // them to a character class.

            loop {
                while self.peek_grapheme(0)? != "*" {
                    self.skip_grapheme()?;
                }

                // skip the "*"
                self.skip_grapheme()?;

                // break if we have "/"
                if self.peek_grapheme(0)? == "/" {
                    self.skip_grapheme()?;
                    break;
                }
            }

            Ok(true)
        } else {
            Ok(false)
        }
    }

    fn get_back_quoted_char(&mut self) -> Result<CompactString, ParserError> {
        let g = self.peek_grapheme(0)?;

        if is_back_quote_grapheme(g) {
            let g = CompactString::new(g);
            let g = self.peek_grapheme(g.len())?;

            if is_back_quote_grapheme(g) {
                self.skip_grapheme()?;
                self.skip_grapheme()?;

                Ok(CompactString::new("`"))
            } else {
                Err(self.unexpected_grapheme(String::from("`")))
            }
        } else if is_single_quote_grapheme(g) {
            self.skip_grapheme()
        } else {
            self.get_non_quote_grapheme(0)
        }
    }

    fn get_back_quoted_item(&mut self) -> Result<Option<CompactString>, ParserError> {
        let g = self.peek_grapheme(0)?;

        if is_backslash_grapheme(g) {
            let g = CompactString::new(g);
            let g = self.peek_grapheme(g.len())?;

            if g == "\n" {
                self.skip_grapheme()?;
                self.skip_grapheme()?;

                Ok(None)
            } else {
                Err(self.unexpected_grapheme(String::from("\\")))
            }
        } else {
            self.get_back_quoted_char().map(Some)
        }
    }

    fn get_back_quoted_string(&mut self) -> Result<CompactString, ParserError> {
        let g = self.peek_grapheme(0)?;

        if is_back_quote_grapheme(g) {
            self.skip_grapheme()?;

            let mut token = CompactString::with_capacity(16);
            consume_graphemes_with!(token, self.get_back_quoted_item());

            let g = self.peek_grapheme(0)?;

            if is_back_quote_grapheme(g) {
                self.skip_grapheme()?;
                Ok(token)
            } else {
                Err({
                    let this = &self;
                    this.located_error(ParserErrorKind::MissingQuote)
                })
            }
        } else {
            let g = g.to_string();
            Err(self.unexpected_grapheme(g))
        }
    }

    fn get_single_quoted_item(&mut self) -> Result<Option<CompactString>, ParserError> {
        let g = self.peek_grapheme(0)?;

        if is_backslash_grapheme(g) {
            let g = CompactString::new(g);
            let g = self.peek_grapheme(g.len())?;

            if g == "\n" {
                self.skip_grapheme()?;
                self.skip_grapheme()?;

                return Ok(None);
            }
        }

        self.get_single_quoted_grapheme(0).map(Some)
    }

    fn get_single_quoted_grapheme(&mut self, at: usize) -> Result<CompactString, ParserError> {
        let g = self.peek_grapheme(at)?;

        if is_single_quote_grapheme(g) {
            let g = CompactString::new(g);
            let g = self.peek_grapheme(at + g.len())?;

            if is_single_quote_grapheme(g) {
                self.skip_graphemes_up_to(at)?;
                self.skip_grapheme()?;
                self.skip_grapheme()?;

                Ok(CompactString::new("'"))
            } else {
                Err(self.unexpected_grapheme(String::from("'")))
            }
        } else if g == "\"" || is_back_quote_grapheme(g) {
            let g = CompactString::new(g);

            self.skip_graphemes_up_to(at)?;
            self.skip_grapheme()?;

            Ok(g)
        } else {
            self.get_non_quote_grapheme(at)
        }
    }

    fn get_double_quoted_item(&mut self) -> Result<Option<CompactString>, ParserError> {
        let g = CompactString::new(self.peek_grapheme(0)?);

        if is_backslash_grapheme(g.as_str()) {
            let g = self.peek_grapheme(g.len())?;

            if g == "\n" {
                self.skip_grapheme()?;
                self.skip_grapheme()?;

                return Ok(None);
            }
        }

        self.get_double_quoted_grapheme().map(Some)
    }

    fn get_double_quoted_grapheme(&mut self) -> Result<CompactString, ParserError> {
        let g = CompactString::new(self.peek_grapheme(0)?);

        if g == "\"" {
            let g = self.peek_grapheme(g.len())?;

            if g != "\"" {
                Err(self.unexpected_grapheme(String::from("\"")))
            } else {
                self.skip_grapheme()?;
                self.skip_grapheme()?;

                Ok(CompactString::new("\""))
            }
        } else if is_single_quote_grapheme(g.as_str()) || is_back_quote_grapheme(g.as_str()) {
            let g = CompactString::new(g);
            self.skip_grapheme()?;
            Ok(g)
        } else {
            self.get_non_quote_grapheme(0)
        }
    }

    fn get_control_escape_sequence(&mut self) -> Result<char, ParserError> {
        let g = self.peek_grapheme(0)?;

        let escaped = match g {
            "a" => '\u{07}', // UTF-8 alert
            "b" => '\u{08}', // UTF-8 backspace
            "v" => '\u{0b}', // UTF-8 vertical tab
            "f" => '\u{0c}', // UTF-8 form feed
            "t" => '\t',
            "n" => '\n',
            "r" => '\r',
            g => {
                let g = String::from(g);
                return Err(self.unexpected_grapheme(g));
            }
        };

        self.skip_grapheme()?;
        Ok(escaped)
    }

    fn get_octal_escape_sequence(&mut self) -> Result<char, ParserError> {
        self.escape_sequence_to_char(|g| is_octal_digit_grapheme(g), 8)
    }

    fn get_hexadecimal_escape_sequence(&mut self) -> Result<char, ParserError> {
        self.skip_grapheme()?;
        let c = self.peek_grapheme(0)?;

        if is_hexadecimal_digit_grapheme(c) {
            self.escape_sequence_to_char(|g| is_hexadecimal_digit_grapheme(g), 16)
        } else {
            Err(self.incomplete_reduction())
        }
    }

    fn escape_sequence_to_char(
        &mut self,
        accept_g: impl Fn(&str) -> bool,
        radix: u32,
    ) -> Result<char, ParserError> {
        let mut c = self.peek_grapheme(0)?;
        let mut token = String::with_capacity(16);

        loop {
            token.push_str(c);

            self.skip_grapheme()?;
            c = self.peek_grapheme(0)?;

            if !accept_g(c) {
                break;
            }
        }

        if is_backslash_grapheme(c) {
            self.skip_grapheme()?;
            u32::from_str_radix(&token, radix).map_or_else(
                |_| Err(self.parse_big_int_error()),
                |n| char::try_from(n).map_err(|_| self.located_error(ParserErrorKind::Utf8Error)),
            )
        } else {
            Err(self.incomplete_reduction())
        }
    }

    fn get_non_quote_grapheme(&mut self, at: usize) -> Result<CompactString, ParserError> {
        let g = self.peek_grapheme(at)?;

        if is_graphic_grapheme(g) || g.is_alphanumeric_grapheme() || is_solo_grapheme(g) || g == " "
        {
            let g = CompactString::new(g);
            self.skip_graphemes_up_to(at)?;
            self.skip_grapheme()?;
            Ok(g)
        } else {
            if !is_backslash_grapheme(g) {
                let c = g.to_string();
                return Err(self.unexpected_grapheme(c));
            }

            self.skip_graphemes_up_to(at)?;
            self.skip_grapheme()?;
            let g = self.peek_grapheme(0)?;

            if is_meta_grapheme(g) {
                let g = CompactString::new(g);
                self.skip_grapheme()?;
                return Ok(g);
            }

            if is_octal_digit_grapheme(g) {
                self.get_octal_escape_sequence()
            } else if is_symbolic_hexadecimal_grapheme(g) {
                self.get_hexadecimal_escape_sequence()
            } else {
                self.get_control_escape_sequence()
            }
            .map(|c| CompactString::from_iter(std::iter::once(c)))
        }
    }

    fn char_code_list_token(&mut self) -> Result<CompactString, ParserError> {
        let mut token = CompactString::with_capacity(16);

        self.skip_grapheme()?; // skip the "" that was peeked
        consume_graphemes_with!(token, self.get_double_quoted_item());

        let g = self.peek_grapheme(0)?;

        if g == "\"" {
            self.skip_grapheme()?;
            Ok(token)
        } else {
            Err({
                let this = &self;
                this.located_error(ParserErrorKind::MissingQuote)
            })
        }
    }

    fn hexadecimal_constant(&mut self) -> Result<NumberToken, ParserError> {
        let g = self.peek_grapheme("x".len())?;

        if is_hexadecimal_digit_grapheme(g) {
            self.skip_grapheme()?; // skip the "x"

            let mut g = self.peek_grapheme(0)?; // appease the borrow checker
            let mut token = CompactString::with_capacity(16);

            loop {
                if is_hexadecimal_digit_grapheme(g) {
                    token.push_str(g);
                    self.skip_grapheme()?;

                    g = match self.peek_grapheme(0) {
                        Ok(g) => g,
                        Err(e) if e.is_unexpected_eof() => {
                            break;
                        }
                        Err(e) => return Err(e),
                    };
                } else {
                    break;
                }
            }

            self.parse_integer_by_radix(&token, 16)
                .map(NumberToken::Integer)
        } else {
            Err(self.parse_big_int_error())
        }
    }

    fn octal_constant(&mut self) -> Result<NumberToken, ParserError> {
        let g = self.peek_grapheme("o".len())?;

        if is_octal_digit_grapheme(g) {
            self.skip_grapheme()?; // skip the "o"

            let mut g = self.peek_grapheme(0)?; // appease the borrow checker
            let mut token = CompactString::with_capacity(16);

            loop {
                if is_octal_digit_grapheme(g) {
                    token.push_str(g);
                    self.skip_grapheme()?;

                    g = match self.peek_grapheme(0) {
                        Ok(c) => c,
                        Err(e) if e.is_unexpected_eof() => {
                            break;
                        }
                        Err(e) => return Err(e),
                    };
                } else {
                    break;
                }
            }

            self.parse_integer_by_radix(&token, 8)
                .map(NumberToken::Integer)
        } else {
            Err(self.parse_big_int_error())
        }
    }

    fn binary_constant(&mut self) -> Result<NumberToken, ParserError> {
        let g = self.peek_grapheme("b".len())?;

        if is_binary_grapheme(g) {
            self.skip_grapheme()?; // skip the "b"
            let mut g = self.peek_grapheme(0)?; // appease the borrow checker
            let mut token = String::with_capacity(16);

            loop {
                if is_binary_grapheme(g) {
                    token.push_str(g);
                    self.skip_grapheme()?;
                    g = match self.peek_grapheme(0) {
                        Ok(c) => c,
                        Err(e) if e.is_unexpected_eof() => {
                            break;
                        }
                        Err(e) => return Err(e),
                    };
                } else {
                    break;
                }
            }

            self.parse_integer_by_radix(&token, 2)
                .map(NumberToken::Integer)
        } else {
            Err(self.parse_big_int_error())
        }
    }

    fn variable_token(&mut self) -> Result<Token, ParserError> {
        let mut token = CompactString::with_capacity(16);
        token.push_str(&self.skip_grapheme()?);

        loop {
            let g = self.peek_grapheme(0)?;

            if g.is_alphanumeric_grapheme() {
                token.push_str(g);
                self.skip_grapheme()?;
            } else {
                break;
            }
        }

        Ok(Token::Var(token))
    }

    fn name_token(&mut self, g: CompactString) -> Result<Token, ParserError> {
        let mut token = CompactString::with_capacity(16);

        if is_lowercase_grapheme(g.as_str()) {
            token.push_str(&g);
            self.skip_grapheme()?;

            loop {
                let g = self.peek_grapheme(0)?;

                if g.is_alphanumeric_grapheme() {
                    token.push_str(&g);
                    self.skip_grapheme()?;
                } else {
                    break;
                }
            }
        } else if is_graphic_token_grapheme(g.as_str()) {
            token.push_str(&g);
            self.skip_grapheme()?;

            loop {
                let g = self.peek_grapheme(0)?;

                if is_graphic_token_grapheme(g) {
                    token.push_str(&g);
                    self.skip_grapheme()?;
                } else {
                    break;
                }
            }
        } else if g == "!" || g == ";" {
            token.push_str(&g);
            self.skip_grapheme()?;
        } else if is_single_quote_grapheme(g.as_str()) {
            self.skip_grapheme()?;
            consume_graphemes_with!(token, self.get_single_quoted_item());

            let g = self.peek_grapheme(0)?;

            if is_single_quote_grapheme(g) {
                self.skip_grapheme()?;

                // use exactly_one once stable in our msrv https://github.com/rust-lang/rust/issues/149266
                if let Some(c) = token.chars().next()
                    && token.chars().nth(1).is_none()
                {
                    let atom = AtomCell::from_codepoint(c).get_name();
                    return Ok(Token::Literal(Literal::Atom(atom)));
                }
            } else {
                let g = g.to_string();
                return Err(self.located_error(ParserErrorKind::InvalidSingleQuotedGrapheme(g)));
            }
        } else {
            match self.get_back_quoted_string() {
                Ok(_) => return Err(self.located_error(ParserErrorKind::BackQuotedString)),
                Err(e) => return Err(e),
            }
        }

        Ok(Token::Literal(Literal::Atom(AtomTable::build_with(
            &self.machine_st.atom_tbl,
            &token,
        ))))
    }

    fn vacate_with_float(
        &mut self,
        token: CompactString,
    ) -> Result<(F64Offset, OrderedFloat<f64>), ParserError> {
        let n = self.parse_float_lossy(&token)?;
        let offset = float_alloc!(n, self.machine_st.arena);

        Ok((offset, OrderedFloat(n)))
    }

    fn skip_underscore_in_number(&mut self) -> Result<CompactString, ParserError> {
        if let g = CompactString::new(self.peek_grapheme(0)?)
            && !is_underscore_grapheme(g.as_str())
        {
            return Ok(g);
        } else {
            self.skip_grapheme()?;
            self.scan_for_layout()?;

            let g = self.peek_grapheme(0)?;

            if is_decimal_digit_grapheme(g) {
                Ok(CompactString::new(g))
            } else {
                Err(self.parse_big_int_error())
            }
        }
    }

    fn parse_integer_by_radix(&mut self, token: &str, radix: u32) -> Result<GInteger, ParserError> {
        i64::from_str_radix(token, radix)
            .map(|n| {
                Fixnum::build_with_checked(n)
                    .map(GInteger::Fixnum)
                    .unwrap_or_else(|_| {
                        GInteger::Integer(arena_alloc!(
                            Integer::from(n),
                            &mut self.machine_st.arena
                        ))
                    })
            })
            .or_else(|_| {
                Integer::from_str_radix(token, radix)
                    .map(|n| GInteger::Integer(arena_alloc!(n, &mut self.machine_st.arena)))
                    .map_err(|_| self.parse_big_int_error())
            })
    }

    #[inline]
    fn parse_integer(&mut self, token: &str) -> Result<GInteger, ParserError> {
        self.parse_integer_by_radix(token, 10)
    }

    fn number_token(&mut self, leading_g: CompactString) -> Result<NumberToken, ParserError> {
        let mut token = CompactString::with_capacity(16);

        self.skip_grapheme()?;
        token.push_str(&leading_g);

        let mut g = try_nt!(token, self.skip_underscore_in_number());

        while is_decimal_digit_grapheme(g.as_str()) {
            token.push_str(g.as_str());
            self.skip_grapheme()?;
            g = try_nt!(token, self.skip_underscore_in_number());
        }

        if g == "." {
            let after_dot_g_opt = self.reader.peek_grapheme(".".len())?;

            if after_dot_g_opt.is_none() {
                self.parse_integer(&token).map(NumberToken::Integer)
            } else if let Some(g) = after_dot_g_opt
                && is_decimal_digit_grapheme(g)
            {
                token.push_str(&self.skip_grapheme()?); // push "."

                let mut g = try_nt!(token, self.peek_grapheme(0));

                while is_decimal_digit_grapheme(g) {
                    token.push_str(g);
                    self.skip_grapheme()?;
                    g = try_nt!(token, self.peek_grapheme(0));
                }

                if is_exponent_grapheme(g) {
                    let exp_g = CompactString::new(g);

                    let next_g = match self.peek_grapheme(exp_g.len()) {
                        Err(_) => {
                            return self
                                .vacate_with_float(token)
                                .map(|(offset, fl)| NumberToken::Float(offset, fl));
                        }
                        Ok(g) => CompactString::new(g),
                    };

                    if !is_sign_grapheme(next_g.as_str())
                        && !is_decimal_digit_grapheme(next_g.as_str())
                    {
                        return self
                            .vacate_with_float(token)
                            .map(|(offset, fl)| NumberToken::Float(offset, fl));
                    }

                    if is_sign_grapheme(next_g.as_str()) {
                        let digit_g = match self.peek_grapheme(exp_g.len() + next_g.len()) {
                            Err(_) => {
                                return self
                                    .vacate_with_float(token)
                                    .map(|(offset, fl)| NumberToken::Float(offset, fl));
                            }
                            Ok(g) => CompactString::new(g),
                        };

                        if !is_decimal_digit_grapheme(digit_g.as_str()) {
                            return self
                                .vacate_with_float(token)
                                .map(|(offset, fl)| NumberToken::Float(offset, fl));
                        }

                        token.push_str(&exp_g);
                        token.push_str(&next_g);

                        self.skip_grapheme()?; // skip exp_g
                        self.skip_grapheme()?; // skip next_g
                    } else {
                        // next_g is a decimal digit
                        token.push_str(&exp_g);
                        self.skip_grapheme()?; // skip exp_g
                    }

                    let g = self.peek_grapheme(0)?;

                    if is_decimal_digit_grapheme(g) {
                        token.push_str(g);
                        self.skip_grapheme()?;

                        loop {
                            let g = try_nt!(token, self.peek_grapheme(0));

                            if is_decimal_digit_grapheme(g) {
                                token.push_str(g);
                                self.skip_grapheme()?;
                            } else {
                                break;
                            }
                        }

                        let n = self.parse_float_lossy(&token)?;
                        let offset = float_alloc!(n, self.machine_st.arena);

                        Ok(NumberToken::Float(offset, OrderedFloat(n)))
                    } else {
                        self.vacate_with_float(token)
                            .map(|(offset, fl)| NumberToken::Float(offset, fl))
                    }
                } else {
                    let n = self.parse_float_lossy(&token)?;
                    let offset = float_alloc!(n, self.machine_st.arena);
                    Ok(NumberToken::Float(offset, OrderedFloat(n)))
                }
            } else {
                self.parse_integer(&token).map(NumberToken::Integer)
            }
        } else if token.starts_with('0') && token.len() == 1 {
            if is_symbolic_hexadecimal_grapheme(g.as_str()) {
                self.hexadecimal_constant().or_else(|e| {
                    if let ParserErrorKind::ParseBigInt = e.kind {
                        self.parse_integer(&token).map(NumberToken::Integer)
                    } else {
                        Err(e)
                    }
                })
            } else if g == "o" {
                self.octal_constant().or_else(|e| {
                    if let ParserErrorKind::ParseBigInt = e.kind {
                        self.parse_integer(&token).map(NumberToken::Integer)
                    } else {
                        Err(e)
                    }
                })
            } else if g == "b" {
                self.binary_constant().or_else(|e| {
                    if let ParserErrorKind::ParseBigInt = e.kind {
                        self.parse_integer(&token).map(NumberToken::Integer)
                    } else {
                        Err(e)
                    }
                })
            } else if is_single_quote_grapheme(g.as_str()) {
                let g = CompactString::new(self.peek_grapheme("'".len())?);

                if is_backslash_grapheme(g.as_str()) {
                    let c = self.peek_grapheme("'\\".len())?; // peek past '\'' *and* '\\'

                    if c == "\n" {
                        return Ok(NumberToken::Integer(GInteger::Fixnum(Fixnum::build_with(
                            0,
                        ))));
                    }
                }

                self.get_single_quoted_grapheme("'".len())
                    .and_then(|g| {
                        grapheme_as_char(g.as_str()).ok_or_else(|| {
                            self.located_error(ParserErrorKind::InvalidSingleQuotedGrapheme(
                                g.to_string(),
                            ))
                        })
                    })
                    .map(|c| NumberToken::Integer(GInteger::Fixnum(Fixnum::build_with(c))))
                    .or_else(|err| {
                        match &err.kind {
                            ParserErrorKind::UnexpectedGrapheme(c)
                                if is_single_quote_grapheme(c.as_str()) => {}
                            _ => return Err(err),
                        }

                        self.parse_integer(&token).map(NumberToken::Integer)
                    })
            } else {
                self.parse_integer(&token).map(NumberToken::Integer)
            }
        } else {
            self.parse_integer(&token).map(NumberToken::Integer)
        }
    }

    fn consume_layout(
        &mut self,
        c: Option<CompactString>,
        layout_info: &mut LayoutInfo,
    ) -> Result<(), ParserError> {
        #[allow(clippy::redundant_guards)]
        match c {
            Some(c) if is_layout_grapheme(c.as_str()) => {
                self.skip_grapheme()?;
                layout_info.inserted = true;
            }
            Some(c) if c == "%" => {
                self.single_line_comment()?;
                layout_info.inserted = true;
            }
            Some(c) if c == "/" => {
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
        match self.peek_grapheme(0) {
            Err(e) => Err(e),
            Ok(c) => {
                let mut layout_info = LayoutInfo {
                    inserted: false,
                    more: true,
                };
                let mut cr = Some(CompactString::new(c));

                loop {
                    self.consume_layout(cr, &mut layout_info)?;

                    if !layout_info.more {
                        break;
                    }

                    cr = self.peek_grapheme(0).ok().map(CompactString::new);
                }

                Ok(layout_info.inserted)
            }
        }
    }

    pub fn next_number_token(&mut self) -> Result<Token, ParserError> {
        self.scan_for_layout()?;
        let g = CompactString::new(self.peek_grapheme(0)?);

        if !is_decimal_digit_grapheme(g.as_str()) {
            return self.name_token(g);
        }

        match self.number_token(g) {
            Ok(NumberToken::Partial(token_string)) => match self.parse_integer(&token_string) {
                Ok(n) => Ok(Token::Literal(n.to_literal())),
                Err(_) => {
                    let n = self.parse_float_lossy(&token_string)?;
                    let offset = float_alloc!(n, self.machine_st.arena);
                    Ok(Token::Literal(Literal::F64(offset, OrderedFloat(n))))
                }
            },
            Ok(NumberToken::Float(offset, n)) => Ok(Token::Literal(Literal::F64(offset, n))),
            Ok(NumberToken::Integer(n)) => Ok(Token::Literal(n.to_literal())),
            Err(e) => Err(e),
        }
    }

    pub fn next_token(&mut self) -> Result<Token, ParserError> {
        let layout_inserted = self.scan_for_layout()?;
        let cr = self.peek_grapheme(0);

        match cr {
            Ok(g) => {
                if is_uppercase_grapheme(g) || is_underscore_grapheme(g) {
                    return self.variable_token();
                }

                if g == "," {
                    self.skip_grapheme()?;
                    return Ok(Token::Comma);
                }

                if g == ")" {
                    self.skip_grapheme()?;
                    return Ok(Token::Close);
                }

                if g == "(" {
                    self.skip_grapheme()?;
                    return Ok(if layout_inserted {
                        Token::Open
                    } else {
                        Token::OpenCT
                    });
                }

                if g == "." {
                    return match self.peek_grapheme(".".len()) {
                        Ok(g) if is_layout_grapheme(g) || g == "%" => {
                            let g = CompactString::new(g);
                            self.skip_grapheme()?; // skip '.'

                            if g == "\n" {
                                self.skip_grapheme()?;
                            }

                            Ok(Token::End)
                        }
                        Err(e) if e.is_unexpected_eof() => {
                            self.skip_grapheme()?;
                            Ok(Token::End)
                        }
                        _ => self.name_token(CompactString::new(".")),
                    };
                }

                if is_decimal_digit_grapheme(g) {
                    let c = CompactString::new(g);
                    return self.number_token(c).and_then(|nt| match nt.to_token() {
                        Some(token) => Ok(token),
                        None => Err(ParserError::unexpected_eof()),
                    });
                }

                if g == "]" {
                    self.skip_grapheme()?;
                    return Ok(Token::CloseList);
                }

                if g == "[" {
                    self.skip_grapheme()?;
                    return Ok(Token::OpenList);
                }

                if g == "|" {
                    self.skip_grapheme()?;
                    let next = self.peek_grapheme(0)?;
                    if next == "|" {
                        self.skip_grapheme()?;
                        return Ok(Token::DoubleBar);
                    }
                    return Ok(Token::HeadTailSeparator);
                }

                if g == "{" {
                    self.skip_grapheme()?;
                    return Ok(Token::OpenCurly);
                }

                if g == "}" {
                    self.skip_grapheme()?;
                    return Ok(Token::CloseCurly);
                }

                if g == "\"" {
                    let string = self.char_code_list_token()?;

                    return if let DoubleQuotes::Atom = self.machine_st.flags.double_quotes {
                        let atom = AtomTable::build_with(&self.machine_st.atom_tbl, &string);
                        Ok(Token::Literal(Literal::Atom(atom)))
                    } else {
                        Ok(Token::String(string))
                    };
                }

                if g == "\u{0}" {
                    return Err(ParserError::unexpected_eof());
                }

                let g = CompactString::new(g);
                self.name_token(g)
            }
            Err(e) => Err(e),
        }
    }

    fn parse_float_lossy(&self, token: &str) -> Result<f64, ParserError> {
        const FORMAT: u128 = lexical::format::STANDARD;
        let Ok(options) = lexical::ParseFloatOptions::builder().lossy(true).build() else {
            return Err(self.located_error(ParserErrorKind::ParseFloat));
        };

        let Ok(n) = lexical::parse_with_options::<f64, _, FORMAT>(token.as_bytes(), &options)
        else {
            return Err(self.located_error(ParserErrorKind::ParseFloat));
        };
        Ok(n)
    }
}
