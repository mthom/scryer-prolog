## WG17 2025 Double Bar Syntax Error Tests
## Reference: https://www.complang.tuwien.ac.at/ulrich/iso-prolog/double_bar
## The || operator is only valid after double-quoted strings

```trycmd
$ scryer-prolog -f --no-add-history tests-pl/double_bar_list1.pl -g halt
   error(syntax_error(incomplete_reduction),read_term/3:2).

```

```trycmd
$ scryer-prolog -f --no-add-history tests-pl/double_bar_list2.pl -g halt
   error(syntax_error(incomplete_reduction),read_term/3:2).

```

```trycmd
$ scryer-prolog -f --no-add-history tests-pl/double_bar_var.pl -g halt
   error(syntax_error(incomplete_reduction),read_term/3:2).

```

```trycmd
$ scryer-prolog -f --no-add-history tests-pl/double_bar_atom.pl -g halt
   error(syntax_error(incomplete_reduction),read_term/3:2).

```

```trycmd
$ scryer-prolog -f --no-add-history tests-pl/double_bar_number.pl -g halt
   error(syntax_error(incomplete_reduction),read_term/3:2).

```
