# Issue #3119: Operators with priority 1000 should not be allowed in lists

## Test that priority 1000 operator in list throws syntax error

```trycmd
$ scryer-prolog -f --no-add-history
?- use_module(library(charsio)).
   true.
?- op(1000,xfx,~>).
   true.
?- read_from_chars("[a~>b].",T).
   error(syntax_error(incomplete_reduction),read_term_from_chars/3:0).
?- halt.
```

## Test that priority 1000 yfx operator in list throws syntax error

```trycmd
$ scryer-prolog -f --no-add-history
?- use_module(library(charsio)).
   true.
?- op(1000,yfx,~>).
   true.
?- read_from_chars("[a~>b].",T).
   error(syntax_error(incomplete_reduction),read_term_from_chars/3:0).
?- halt.
```

## Test that priority 999 operator in list works

```trycmd
$ scryer-prolog -f --no-add-history
?- use_module(library(charsio)).
   true.
?- op(999,xfx,~>).
   true.
?- read_from_chars("[a~>b].",T).
   T = [a~>b].
?- halt.
```

## Test that parenthesized priority 1000 operator in list works

```trycmd
$ scryer-prolog -f --no-add-history
?- use_module(library(charsio)).
   true.
?- op(1000,xfx,~>).
   true.
?- read_from_chars("[(a~>b)].",T).
   T = [a~>b].
?- halt.
```
