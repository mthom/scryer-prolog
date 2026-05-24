# Issue #3119: Operators with priority 1000 should not be allowed in lists

## Test that priority 1000 operator in list throws syntax error

```trycmd
$ scryer-prolog -f --no-add-history -g "use_module(library(charsio)), op(1000,xfx,~>), read_from_chars(\"[a~>b].\",T), halt"
use_module(library(charsio)),op(1000,xfx,~>),read_from_chars("[a~>b].",T),halt causes: error(syntax_error(incomplete_reduction),read_term_from_chars/3:0)

```

## Test that priority 1000 yfx operator in list throws syntax error

```trycmd
$ scryer-prolog -f --no-add-history -g "use_module(library(charsio)), op(1000,yfx,~>), read_from_chars(\"[a~>b].\",T), halt"
use_module(library(charsio)),op(1000,yfx,~>),read_from_chars("[a~>b].",T),halt causes: error(syntax_error(incomplete_reduction),read_term_from_chars/3:0)

```

## Test that priority 999 operator in list works

```trycmd
$ scryer-prolog -f --no-add-history -g "use_module(library(charsio)), op(999,xfx,~>), read_from_chars(\"[a~>b].\",T), writeq(T), nl, halt"
[a~>b]

```

## Test that parenthesized priority 1000 operator in list works

```trycmd
$ scryer-prolog -f --no-add-history -g "use_module(library(charsio)), op(1000,xfx,~>), read_from_chars(\"[(a~>b)].\",T), writeq(T), nl, halt"
[(a~>b)]

```
