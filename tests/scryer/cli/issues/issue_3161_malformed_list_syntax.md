# Issue 3161: Malformed List Syntax in Curly Braces

Tests for the parser bug where malformed list syntax like `[|]` was incorrectly
accepted inside curly braces when preceded by specific operator patterns.

## Test that {!*[|]*} throws syntax error

Before the fix, this incorrectly evaluated to `T = {*}`.
After the fix, it should throw a syntax error.

```trycmd
$ scryer-prolog -f --no-add-history -g "use_module(library(dcgs)), {!*[|]*}=T, halt"
use_module(library(dcgs)),{!*[|]*}=T,halt causes: error(syntax_error(incomplete_reduction),read_term/3:1)

```

## Test that {!+[|]+} throws syntax error

```trycmd
$ scryer-prolog -f --no-add-history -g "use_module(library(dcgs)), {!+[|]+}=T, halt"
use_module(library(dcgs)),{!+[|]+}=T,halt causes: error(syntax_error(incomplete_reduction),read_term/3:1)

```

## Test that {[|]} throws syntax error

```trycmd
$ scryer-prolog -f --no-add-history -g "{[|]}=T, halt"
"{[|]}=T,halt" cannot be read: error(syntax_error(incomplete_reduction),read_term/3:1)

```

## Test that valid list syntax still works

```trycmd
$ scryer-prolog -f --no-add-history -g "{[a,b,c]}=T, write(T), nl, halt"
{[a,b,c]}

```

## Test that empty list in curly braces works

```trycmd
$ scryer-prolog -f --no-add-history -g "{[]}=T, write(T), nl, halt"
{[]}

```

## Test that cut in curly braces works

```trycmd
$ scryer-prolog -f --no-add-history -g "{!}=T, write(T), nl, halt"
{!}

```
