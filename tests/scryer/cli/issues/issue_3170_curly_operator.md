# Issue #3170: Curly brace operator priority limits

## Test that built-in priority 1200 operators work in curly braces

### Test :- operator (priority 1200)

```trycmd
$ scryer-prolog -f --no-add-history -g "use_module(library(charsio)), read_from_chars(\"{a:-b}.\",T), writeq(T), nl, halt"
{a:-b}

```

### Test --> operator (priority 1200)

```trycmd
$ scryer-prolog -f --no-add-history -g "use_module(library(charsio)), read_from_chars(\"{a-->b}.\",T), writeq(T), nl, halt"
{a-->b}

```

## Test that user-defined priority 1200 operators work in curly braces

```trycmd
$ scryer-prolog -f --no-add-history -g "use_module(library(charsio)), op(1200,xfx,~>), read_from_chars(\"{a~>b}.\",T), writeq(T), nl, halt"
{a~>b}

```

## Test that priority 1199 operators work in curly braces

```trycmd
$ scryer-prolog -f --no-add-history -g "use_module(library(charsio)), op(1199,xfx,~>), read_from_chars(\"{a~>b}.\",T), writeq(T), nl, halt"
{a~>b}

```

## Test that parenthesized priority 1200 operators work

```trycmd
$ scryer-prolog -f --no-add-history -g "use_module(library(charsio)), op(1200,xfx,~>), read_from_chars(\"{(a~>b)}.\",T), writeq(T), nl, halt"
{a~>b}

```

## Test that priority 1201 operators fail (if definable)

```trycmd
$ scryer-prolog -f --no-add-history -g "op(1201,xfx,~>), halt"
op(1201,xfx,~>),halt causes: error(domain_error(operator_priority,1201),op/3)

```
