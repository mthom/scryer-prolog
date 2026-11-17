# Issue #3156: Bracketed terms should not be usable as functors

## Test that ((>)(1) throws syntax error

```trycmd
$ scryer-prolog -f --no-add-history
?- use_module(library(charsio)).
   true.
?- read_from_chars("((>)(1).",T).
   error(syntax_error(incomplete_reduction),read_term_from_chars/3:0).
?- halt.
```

## Test that ((a)(b) throws syntax error

```trycmd
$ scryer-prolog -f --no-add-history
?- use_module(library(charsio)).
   true.
?- read_from_chars("((a)(b).",T).
   error(syntax_error(incomplete_reduction),read_term_from_chars/3:0).
?- halt.
```

## Test that valid functor application still works

```trycmd
$ scryer-prolog -f --no-add-history
?- use_module(library(charsio)).
   true.
?- read_from_chars("a(b).",T).
   T = a(b).
?- halt.
```

## Test that simple bracketed terms work

```trycmd
$ scryer-prolog -f --no-add-history
?- use_module(library(charsio)).
   true.
?- read_from_chars("(a).",T).
   T = a.
?- halt.
```

## Test that (a) (b) with space throws syntax error

```trycmd
$ scryer-prolog -f --no-add-history
?- use_module(library(charsio)).
   true.
?- read_from_chars("(a) (b).",T).
   error(syntax_error(incomplete_reduction),read_term_from_chars/3:0).
?- halt.
```

## Test that bracketed operator works

```trycmd
$ scryer-prolog -f --no-add-history
?- use_module(library(charsio)).
   true.
?- read_from_chars("((>)).",T).
   T = (>).
?- halt.
```
