# Issue #3170: Enforce priority 1199 limit in curly braces

## Test that priority 1200 operator in curly braces throws syntax error

```trycmd
$ scryer-prolog -f --no-add-history
?- use_module(library(charsio)).
   true.
?- op(1200,xfx,~>).
   true.
?- read_from_chars("{a~>b}.",T).
   error(syntax_error(incomplete_reduction),read_term_from_chars/3:0).
?- halt.
```

## Test that priority 1199 operator in curly braces works

```trycmd
$ scryer-prolog -f --no-add-history
?- use_module(library(charsio)).
   true.
?- op(1199,xfx,~>).
   true.
?- read_from_chars("{a~>b}.",T).
   T = {a~>b}.
?- halt.
```

## Test that parenthesized priority 1200 operator in curly braces works

```trycmd
$ scryer-prolog -f --no-add-history
?- use_module(library(charsio)).
   true.
?- op(1200,xfx,~>).
   true.
?- read_from_chars("{(a~>b)}.",T).
   T = {a~>b}.
?- halt.
```
