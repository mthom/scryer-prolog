#[inline]
pub fn grapheme_as_char(c: &str) -> Option<char> {
    let mut iter = c.chars();

    if let Some(c) = iter.next()
        && iter.next().is_none()
    {
        return Some(c);
    }

    None
}

pub trait MatchGrapheme: Copy {
    fn is_alphabetic_grapheme(self) -> bool;
    fn is_alphanumeric_grapheme(self) -> bool;

    fn matches_char_pred(self, f: impl FnOnce(char) -> bool) -> bool;
    #[allow(dead_code)]
    fn matches_str_pred(self, f: impl FnOnce(&str) -> bool) -> bool;
}

// Scryer's ISO Prolog parser deals in characters as graphemes (&'a
// str) while the rest of Scryer deals in characters as codepoints
// (char). Character predicates must always agree in both settings,
// however, which we ensure via the MatchGrapheme trait, since the
// Pattern trait isn't yet in stable Rust
// (https://github.com/rust-lang/rust/issues/27721).

impl MatchGrapheme for char {
    #[inline]
    fn is_alphabetic_grapheme(self) -> bool {
        self == '_' || self.is_alphabetic()
    }

    #[inline]
    fn is_alphanumeric_grapheme(self) -> bool {
        self == '_' || self.is_alphanumeric()
    }

    #[inline]
    fn matches_char_pred(self, f: impl FnOnce(char) -> bool) -> bool {
        f(self)
    }

    #[inline]
    fn matches_str_pred(self, f: impl FnOnce(&str) -> bool) -> bool {
        let mut buf = [0u8; 4];
        f(self.encode_utf8(&mut buf))
    }
}

impl MatchGrapheme for &'_ str {
    #[inline]
    fn is_alphabetic_grapheme(self) -> bool {
        self.chars()
            .next()
            .is_some_and(|c| c.is_alphabetic_grapheme())
    }

    #[inline]
    fn is_alphanumeric_grapheme(self) -> bool {
        self.chars()
            .next()
            .is_some_and(|c| c.is_alphanumeric_grapheme())
    }

    #[inline]
    fn matches_char_pred(self, f: impl FnOnce(char) -> bool) -> bool {
        self.chars().next().is_some_and(f) && self.chars().nth(1).is_none()
    }

    #[inline]
    fn matches_str_pred(self, f: impl FnOnce(&str) -> bool) -> bool {
        f(self)
    }
}

#[inline]
pub fn is_layout_grapheme<G: MatchGrapheme>(g: G) -> bool {
    g.matches_char_pred(|c| matches!(c, ' ' | '\r' | '\n' | '\t' | '\x0B' | '\x0C'))
}

#[inline]
pub fn is_meta_grapheme<G: MatchGrapheme>(g: G) -> bool {
    g.matches_char_pred(|c| matches!(c, '\\' | '\'' | '"' | '`'))
}

#[inline]
pub fn is_octal_digit_grapheme<G: MatchGrapheme>(g: G) -> bool {
    g.matches_char_pred(|c| matches!(c, '0'..='7'))
}

#[inline]
pub fn is_octet_grapheme<G: MatchGrapheme>(g: G) -> bool {
    g.matches_char_pred(|c| matches!(c, '\u{0000}'..='\u{00FF}'))
}

#[inline]
pub fn is_binary_grapheme<G: MatchGrapheme>(g: G) -> bool {
    g.matches_char_pred(|c| matches!(c, '0' | '1'))
}

#[inline]
pub fn is_hexadecimal_digit_grapheme<G: MatchGrapheme>(g: G) -> bool {
    g.matches_char_pred(|c| matches!(c, '0'..='9' | 'A'..='F' | 'a'..='f'))
}

#[inline]
pub fn is_solo_grapheme<G: MatchGrapheme>(g: G) -> bool {
    g.matches_char_pred(|c| {
        matches!(
            c,
            '!' | '(' | ')' | ',' | ';' | '[' | ']' | '{' | '}' | '|' | '%'
        )
    })
}

#[inline]
pub fn is_symbol_control_grapheme<G: MatchGrapheme>(g: G) -> bool {
    g.matches_char_pred(|c| matches!(c, 'a' | 'b' | 'f' | 'n' | 'r' | 't' | 'v' | '0'))
}

#[inline]
pub fn is_sign_grapheme<G: MatchGrapheme>(g: G) -> bool {
    g.matches_char_pred(|c| matches!(c, '+' | '-'))
}

#[inline]
pub fn is_graphic_grapheme<G: MatchGrapheme>(g: G) -> bool {
    g.matches_char_pred(|c| {
        matches!(
            c,
            '#' | '$'
                | '&'
                | '*'
                | '+'
                | '-'
                | '.'
                | '/'
                | ':'
                | '<'
                | '='
                | '>'
                | '?'
                | '@'
                | '^'
                | '~'
        )
    })
}

#[inline]
pub fn is_symbolic_hexadecimal_grapheme<G: MatchGrapheme>(g: G) -> bool {
    g.matches_char_pred(|c| c == 'x')
}

#[inline]
pub fn is_semicolon_grapheme<G: MatchGrapheme>(g: G) -> bool {
    g.matches_char_pred(|c| c == ';')
}

#[inline]
pub fn is_graphic_token_grapheme<G: MatchGrapheme>(g: G) -> bool {
    g.matches_char_pred(|c| c == '\\') || is_graphic_grapheme(g)
}

#[inline]
pub fn is_prolog_grapheme<G: MatchGrapheme>(g: G) -> bool {
    is_graphic_grapheme(g)
        || g.is_alphanumeric_grapheme()
        || is_solo_grapheme(g)
        || is_layout_grapheme(g)
        || is_meta_grapheme(g)
}

#[inline]
pub fn is_exponent_grapheme<G: MatchGrapheme>(g: G) -> bool {
    g.matches_char_pred(|c| matches!(c, 'E' | 'e'))
}

#[inline]
pub fn is_cut_grapheme<G: MatchGrapheme>(g: G) -> bool {
    g.matches_char_pred(|c| c == '!')
}

#[inline]
pub fn is_back_quote_grapheme<G: MatchGrapheme>(g: G) -> bool {
    g.matches_char_pred(|c| c == '`')
}

#[inline]
pub fn is_backslash_grapheme<G: MatchGrapheme>(g: G) -> bool {
    g.matches_char_pred(|c| c == '\\')
}

#[inline]
pub fn is_underscore_grapheme<G: MatchGrapheme>(g: G) -> bool {
    g.matches_char_pred(|c| c == '_')
}

#[inline]
pub fn is_single_quote_grapheme<G: MatchGrapheme>(g: G) -> bool {
    g.matches_char_pred(|c| c == '\'')
}

#[inline]
pub fn is_decimal_digit_grapheme<G: MatchGrapheme>(g: G) -> bool {
    g.matches_char_pred(|c| c.is_ascii_digit())
}

#[inline]
pub fn is_uppercase_grapheme<G: MatchGrapheme>(g: G) -> bool {
    g.matches_char_pred(|c| c.is_uppercase())
}

#[inline]
pub fn is_lowercase_grapheme<G: MatchGrapheme>(g: G) -> bool {
    g.matches_char_pred(|c| c.is_lowercase())
}
