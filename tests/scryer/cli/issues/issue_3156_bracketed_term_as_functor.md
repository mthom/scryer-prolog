# Issue #3156: Bracketed terms should not be usable as functors

## Test that ((>)(1) throws syntax error

```trycmd
$ scryer-prolog -f --no-add-history -g "use_module(library(charsio)), read_from_chars(\"((>)(1).\",T), halt"
use_module(library(charsio)),read_from_chars("((>)(1).",T),halt causes: error(syntax_error(incomplete_reduction),read_term_from_chars/3:0)

```

## Test that ((a)(b) throws syntax error

```trycmd
$ scryer-prolog -f --no-add-history -g "use_module(library(charsio)), read_from_chars(\"((a)(b).\",T), halt"
use_module(library(charsio)),read_from_chars("((a)(b).",T),halt causes: error(syntax_error(incomplete_reduction),read_term_from_chars/3:0)

```

## Test that valid functor application still works

```trycmd
$ scryer-prolog -f --no-add-history -g "use_module(library(charsio)), read_from_chars(\"a(b).\",T), writeq(T), nl, halt"
a(b)

```

## Test that simple bracketed terms work

```trycmd
$ scryer-prolog -f --no-add-history -g "use_module(library(charsio)), read_from_chars(\"(a).\",T), writeq(T), nl, halt"
a

```

## Test that (a) (b) with space throws syntax error

```trycmd
$ scryer-prolog -f --no-add-history -g "use_module(library(charsio)), read_from_chars(\"(a) (b).\",T), halt"
use_module(library(charsio)),read_from_chars("(a) (b).",T),halt causes: error(syntax_error(incomplete_reduction),read_term_from_chars/3:0)

```

## Test that bracketed operator works

```trycmd
$ scryer-prolog -f --no-add-history -g "use_module(library(charsio)), read_from_chars(\"((>)).\",T), writeq(T), nl, halt"
>

```
