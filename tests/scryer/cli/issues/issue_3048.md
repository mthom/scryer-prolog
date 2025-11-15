Bound Variables are sometimes not considered ground even though they should be ground.

```trycmd
$ scryer-prolog -f --no-add-history original.pl -g test -g halt

```

```trycmd
$ scryer-prolog -f --no-add-history original_alt.pl -g test -g halt

```

```trycmd
$ scryer-prolog -f --no-add-history minimize1.pl -g test -g halt

```

```trycmd
$ scryer-prolog -f --no-add-history minimize_final.pl -g test -g halt

```

```trycmd
$ scryer-prolog -f --no-add-history pair_string_key.pl -g test -g halt

```

```trycmd
$ scryer-prolog -f --no-add-history compare.pl -g test -g halt

```

```trycmd
$ scryer-prolog -f --no-add-history compare_get_assoc.pl -g test -g halt

```