# Issue 3161: Malformed List Syntax in Curly Braces

Tests for the parser bug where malformed list syntax like `[|]` was incorrectly
accepted inside curly braces when preceded by specific operator patterns.

## Test that {!*[|]*} throws syntax error

Before the fix, this incorrectly evaluated to `T = {*}`.
After the fix, it should throw a syntax error.

```trycmd
$ scryer-prolog -f --no-add-history
?- use_module(library(dcgs)).
   true.
?- {!*[|]*}=T.
error(syntax_error(incomplete_reduction),read_term/3:1).
?- halt.
```

## Test that {!+[|]+} throws syntax error

```trycmd
$ scryer-prolog -f --no-add-history
?- use_module(library(dcgs)).
   true.
?- {!+[|]+}=T.
error(syntax_error(incomplete_reduction),read_term/3:1).
?- halt.
```

## Test that {[|]} throws syntax error

```trycmd
$ scryer-prolog -f --no-add-history
?- {[|]}=T.
error(syntax_error(incomplete_reduction),read_term/3:1).
?- halt.
```

## Test that valid list syntax still works

```trycmd
$ scryer-prolog -f --no-add-history
?- {[a,b,c]}=T, write(T), nl.
{[a,b,c]}
   T = {"abc"}.
?- halt.
```

## Test that empty list in curly braces works

```trycmd
$ scryer-prolog -f --no-add-history
?- {[]}=T, write(T), nl.
{[]}
   T = {[]}.
?- halt.
```

## Test that cut in curly braces works

```trycmd
$ scryer-prolog -f --no-add-history
?- {!}=T, write(T), nl.
{!}
   T = {!}.
?- halt.
```
