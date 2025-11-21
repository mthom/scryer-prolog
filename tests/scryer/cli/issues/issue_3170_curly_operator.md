# Issue #3170: Operators with priority 1200 should not be allowed in curly braces

## Test that priority 1200 operator in curly braces throws syntax error

```trycmd
$ scryer-prolog -f --no-add-history -g "use_module(library(charsio)), op(1200,xfx,~>), read_from_chars(\"{a~>b}.\",T), halt"
use_module(library(charsio)),op(1200,xfx,~>),read_from_chars("{a~>b}.",T),halt causes: error(syntax_error(incomplete_reduction),read_term_from_chars/3:0)

```

## Test that priority 1199 operator in curly braces works

```trycmd
$ scryer-prolog -f --no-add-history -g "use_module(library(charsio)), op(1199,xfx,~>), read_from_chars(\"{a~>b}.\",T), writeq(T), nl, halt"
{a~>b}

```

## Test that parenthesized priority 1200 operator in curly braces works

```trycmd
$ scryer-prolog -f --no-add-history -g "use_module(library(charsio)), op(1200,xfx,~>), read_from_chars(\"{(a~>b)}.\",T), writeq(T), nl, halt"
{a~>b}

```
