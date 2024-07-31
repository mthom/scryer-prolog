```trycmd
$ scryer-prolog -f --no-add-history tests-pl/invalid_decl1.pl -g halt
   error(syntax_error(invalid_op_decl(specification,invalid_value(moin))),load/1).

```

```trycmd
$ scryer-prolog -f --no-add-history tests-pl/invalid_decl2.pl -g halt
   error(syntax_error(invalid_op_decl(precedence,expected_integer_in_range_0_to_1200)),load/1).

```

```trycmd
$ scryer-prolog -f --no-add-history tests-pl/invalid_decl3.pl -g halt
   error(syntax_error(invalid_op_decl(name,expected_string_or_atom)),load/1).

```

```trycmd
$ scryer-prolog -f --no-add-history tests-pl/invalid_decl4.pl -g halt
   error(syntax_error(existence_error(declaration,op/4)),load/1).

```

```trycmd
$ scryer-prolog -f --no-add-history tests-pl/invalid_decl5.pl -g halt
   error(syntax_error(existence_error(declaration,(;)/2)),load/1).

```

```trycmd
$ scryer-prolog -f --no-add-history tests-pl/invalid_decl6.pl -g halt
   error(syntax_error(not_a_declaration),load/1).

```