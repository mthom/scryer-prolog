```trycmd
$ scryer-prolog -f --no-add-history tests-pl/invalid_decl1.pl -g halt
   error(domain_error(operator_specifier,moin),load/1).

```

```trycmd
$ scryer-prolog -f --no-add-history tests-pl/invalid_decl2.pl -g halt
   error(domain_error(operator_priority,4000),load/1).

```

```trycmd
$ scryer-prolog -f --no-add-history tests-pl/invalid_decl3.pl -g halt
   error(type_error(list,todo_insert_invalid_term_here),load/1).

```

```trycmd
$ scryer-prolog -f --no-add-history tests-pl/invalid_decl4.pl -g halt
   error(existence_error(declaration,op/4),load/1).

```

```trycmd
$ scryer-prolog -f --no-add-history tests-pl/invalid_decl5.pl -g halt
   error(existence_error(declaration,(;)/2),load/1).

```

```trycmd
$ scryer-prolog -f --no-add-history tests-pl/invalid_decl6.pl -g halt
   error(type_error(declaration,todo_insert_invalid_term_here),load/1).

```

```trycmd
$ scryer-prolog -f --no-add-history tests-pl/invalid_decl7.pl -g halt
   error(domain_error(operator_specifier,todo_insert_invalid_term_here),load/1).

```

```trycmd
$ scryer-prolog -f --no-add-history tests-pl/invalid_decl8.pl -g halt
% Warning: singleton variables Var at line 0 of invalid_decl8.pl
   error(domain_error(operator_specifier,todo_insert_invalid_term_here),load/1).

```

```trycmd
$ scryer-prolog -f --no-add-history tests-pl/invalid_decl9.pl -g halt
% Warning: singleton variables Var at line 0 of invalid_decl9.pl
   error(type_error(integer,todo_insert_invalid_term_here),load/1).

```

```trycmd
$ scryer-prolog -f --no-add-history tests-pl/invalid_decl10.pl -g halt

```

The following test doesn't appear to terminate so its moved to a block quote for now

> ```trycmd
> $ scryer-prolog -f --no-add-history tests-pl/invalid_decl11.pl -g halt
> % Warning: singleton variables Var at line 0 of invalid_decl11.pl
>    error(instantiation_error,load/1).
> ```
