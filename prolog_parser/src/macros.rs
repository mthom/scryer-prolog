#[macro_export]
macro_rules! char_class {
    ($c: expr, [$head:expr]) => ($c == $head);
    ($c: expr, [$head:expr $(, $cs:expr)+]) => ($c == $head || char_class!($c, [$($cs),*]));
}

#[macro_export]
macro_rules! symbolic_control_char {
    ($c: expr) => (char_class!($c, ['a', 'b', 'f', 'n', 'r', 't', 'v', '0']))
}

#[macro_export]
macro_rules! space_char {
    ($c: expr) => ($c == ' ')
}

#[macro_export]
macro_rules! layout_char {
    ($c: expr) => (char_class!($c, [' ', '\n', '\t', '\u{0B}', '\u{0C}']))
}

#[macro_export]
macro_rules! symbolic_hexadecimal_char {
    ($c: expr) => ($c == 'x')
}

#[macro_export]
macro_rules! octal_digit_char {
    ($c: expr) => ($c >= '0' && $c <= '7')
}

#[macro_export]
macro_rules! binary_digit_char {
    ($c: expr) => ($c >= '0' && $c <= '1')
}

#[macro_export]
macro_rules! hexadecimal_digit_char {
    ($c: expr) => ($c >= '0' && $c <= '9' ||
                   $c >= 'A' && $c <= 'F' ||
                   $c >= 'a' && $c <= 'f')
}

#[macro_export]
macro_rules! exponent_char {
    ($c: expr) => ($c == 'e' || $c == 'E')
}

#[macro_export]
macro_rules! sign_char {
    ($c: expr) => ($c == '-' || $c == '+')
}

#[macro_export]
macro_rules! new_line_char {
    ($c: expr) => ($c == '\n')
}

#[macro_export]
macro_rules! end_line_comment_char {
    ($c: expr) => ($c == '%')
}

#[macro_export]
macro_rules! comment_1_char {
    ($c: expr) => ($c == '/')
}

#[macro_export]
macro_rules! comment_2_char {
    ($c: expr) => ($c == '*')
}

#[macro_export]
macro_rules! capital_letter_char {
    ($c: expr) => ($c >= 'A' && $c <= 'Z')
}

#[macro_export]
macro_rules! small_letter_char {
    ($c: expr) => ($c >= 'a' && $c <= 'z')
}

#[macro_export]
macro_rules! variable_indicator_char {
    ($c: expr) => ($c == '_')
}

#[macro_export]
macro_rules! graphic_char {
    ($c: expr) => (char_class!($c, ['#', '$', '&', '*', '+', '-', '.', '/', ':',
                                    '<', '=', '>', '?', '@', '^', '~']))
}

#[macro_export]
macro_rules! graphic_token_char {
    ($c: expr) => (graphic_char!($c) || backslash_char!($c))
}

#[macro_export]
macro_rules! alpha_char {
    ($c: expr) =>
        (match $c {
            'a' ..= 'z' => true,
            'A' ..= 'Z' => true,
            '_' => true,
            '\u{00A0}' ..= '\u{00BF}' => true,
            '\u{00C0}' ..= '\u{00D6}' => true,
            '\u{00D8}' ..= '\u{00F6}' => true,
            '\u{00F8}' ..= '\u{00FF}' => true,
            '\u{0100}' ..= '\u{017F}' => true, // Latin Extended-A
            '\u{0180}' ..= '\u{024F}' => true, // Latin Extended-B
            '\u{0250}' ..= '\u{02AF}' => true, // IPA Extensions
            '\u{02B0}' ..= '\u{02FF}' => true, // Spacing Modifier Letters
            '\u{0300}' ..= '\u{036F}' => true, // Combining Diacritical Marks
            '\u{0370}' ..= '\u{03FF}' => true, // Greek/Coptic
            '\u{0400}' ..= '\u{04FF}' => true, // Cyrillic
            '\u{0500}' ..= '\u{052F}' => true, // Cyrillic Supplement
            '\u{0530}' ..= '\u{058F}' => true, // Armenian
            '\u{0590}' ..= '\u{05FF}' => true, // Hebrew
            '\u{0600}' ..= '\u{06FF}' => true, // Arabic
            '\u{0700}' ..= '\u{074F}' => true, // Syriac
            _ => false
        })
}

#[macro_export]
macro_rules! decimal_digit_char {
    ($c: expr) => ($c >= '0' && $c <= '9')
}

#[macro_export]
macro_rules! decimal_point_char {
    ($c: expr) => ($c == '.')
}

#[macro_export]
macro_rules! alpha_numeric_char {
    ($c: expr) => (alpha_char!($c) || decimal_digit_char!($c))
}

#[macro_export]
macro_rules! cut_char {
    ($c: expr) => ($c == '!')
}

#[macro_export]
macro_rules! semicolon_char {
    ($c: expr) => ($c == ';')
}

#[macro_export]
macro_rules! backslash_char {
    ($c: expr) => ($c == '\\')
}

#[macro_export]
macro_rules! single_quote_char {
    ($c: expr) => ($c == '\'')
}

#[macro_export]
macro_rules! double_quote_char {
    ($c: expr) => ($c == '"')
}

#[macro_export]
macro_rules! back_quote_char {
    ($c: expr) => ($c == '`')
}

#[macro_export]
macro_rules! meta_char {
    ($c: expr) => ( char_class!($c, ['\\', '\'', '"', '`']) )
}

#[macro_export]
macro_rules! solo_char {
    ($c: expr) => ( char_class!($c, ['!', '(', ')', ',', ';', '[', ']',
                                     '{', '}', '|', '%']) )
}

#[macro_export]
macro_rules! prolog_char {
    ($c: expr) => (graphic_char!($c) || alpha_numeric_char!($c) || solo_char!($c) ||
                   layout_char!($c) || meta_char!($c))
}
