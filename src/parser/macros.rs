macro_rules! char_class {
    ($c: expr, [$head:expr]) => ($c == $head);
    ($c: expr, [$head:expr $(, $cs:expr)+]) => ($c == $head || char_class!($c, [$($cs),*]));
}

macro_rules! alpha_char {
    ($c: expr) => {
        (!$c.is_numeric()
            && !$c.is_whitespace()
            && !$c.is_control()
            && !graphic_token_char!($c)
            && !layout_char!($c)
            && !meta_char!($c)
            && !solo_char!($c))
            || $c == '_'
    };
}

macro_rules! alpha_numeric_char {
    ($c: expr) => {
        alpha_char!($c) || $c.is_numeric()
    };
}

macro_rules! backslash_char {
    ($c: expr) => {
        $c == '\\'
    };
}

macro_rules! back_quote_char {
    ($c: expr) => {
        $c == '`'
    };
}

macro_rules! octet_char {
    ($c: expr) => {
        ('\u{0000}'..='\u{00FF}').contains(&$c)
    };
}

macro_rules! capital_letter_char {
    ($c: expr) => {
        $c.is_uppercase()
    };
}

macro_rules! comment_1_char {
    ($c: expr) => {
        $c == '/'
    };
}

macro_rules! comment_2_char {
    ($c: expr) => {
        $c == '*'
    };
}

macro_rules! cut_char {
    ($c: expr) => {
        $c == '!'
    };
}

macro_rules! decimal_digit_char {
    ($c: expr) => {
        $c.is_ascii_digit()
    };
}

macro_rules! decimal_point_char {
    ($c: expr) => {
        $c == '.'
    };
}

macro_rules! double_quote_char {
    ($c: expr) => {
        $c == '"'
    };
}

macro_rules! end_line_comment_char {
    ($c: expr) => {
        $c == '%'
    };
}

macro_rules! exponent_char {
    ($c: expr) => {
        $c == 'e' || $c == 'E'
    };
}

macro_rules! graphic_char {
    ($c: expr) => (char_class!($c, ['#', '$', '&', '*', '+', '-', '.', '/', ':',
                                            '<', '=', '>', '?', '@', '^', '~']))
}

macro_rules! graphic_token_char {
    ($c: expr) => {
        graphic_char!($c) || backslash_char!($c)
    };
}

macro_rules! hexadecimal_digit_char {
    ($c: expr) => {
        $c.is_ascii_digit() || ('A'..='F').contains(&$c) || ('a'..='f').contains(&$c)
    };
}

macro_rules! layout_char {
    ($c: expr) => {
        char_class!($c, [' ', '\r', '\n', '\t', '\u{0B}', '\u{0C}'])
    };
}

macro_rules! meta_char {
    ($c: expr) => {
        char_class!($c, ['\\', '\'', '"', '`'])
    };
}

macro_rules! new_line_char {
    ($c: expr) => {
        $c == '\n'
    };
}

macro_rules! octal_digit_char {
    ($c: expr) => {
        ('0'..='7').contains(&$c)
    };
}

macro_rules! binary_digit_char {
    ($c: expr) => {
        $c == '0' || $c == '1'
    };
}

macro_rules! prolog_char {
    ($c: expr) => {
        graphic_char!($c)
            || alpha_numeric_char!($c)
            || solo_char!($c)
            || layout_char!($c)
            || meta_char!($c)
    };
}

macro_rules! semicolon_char {
    ($c: expr) => {
        $c == ';'
    };
}

macro_rules! sign_char {
    ($c: expr) => {
        $c == '-' || $c == '+'
    };
}

macro_rules! single_quote_char {
    ($c: expr) => {
        $c == '\''
    };
}

macro_rules! small_letter_char {
    ($c: expr) => {
        $c.is_alphabetic() && !$c.is_uppercase()
    };
}

macro_rules! solo_char {
    ($c: expr) => {
        char_class!($c, ['!', '(', ')', ',', ';', '[', ']', '{', '}', '|', '%'])
    };
}

macro_rules! space_char {
    ($c: expr) => {
        $c == ' '
    };
}

macro_rules! symbolic_control_char {
    ($c: expr) => {
        char_class!($c, ['a', 'b', 'f', 'n', 'r', 't', 'v', '0'])
    };
}

macro_rules! symbolic_hexadecimal_char {
    ($c: expr) => {
        $c == 'x'
    };
}

macro_rules! variable_indicator_char {
    ($c: expr) => {
        $c == '_'
    };
}
