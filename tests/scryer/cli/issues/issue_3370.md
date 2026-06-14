By the standard, builtin properties are not visible:

```trycmd
$ scryer-prolog -f --no-add-history -g 'current_predicate(true/0), write(fail); write(ok).'
ok
```

Non-existent predicates will not succeed:

```trycmd
$ scryer-prolog -f --no-add-history -g 'current_predicate(abracadabra/0), write(fail); write(ok).'
ok
```

# Issues associated with call

Unsuccessful call should not affect subsequent results of `current_predicate/1`

```trycmd
$ scryer-prolog -f --no-add-history -g 'catch(call(a),_,true), current_predicate(a/0), write(fail); write(ok).'
ok
```

```trycmd
$ scryer-prolog -f --no-add-history -g 'catch(call(foo:a),_,true), current_predicate(foo:a/0), write(fail); write(ok).'
ok
```

```trycmd
$ scryer-prolog -f --no-add-history -g 'catch(call(a, b),_,true), (current_predicate(a/0); current_predicate(b/0)), write(fail); write(ok).'
ok
```

# Issues associated with consult

```trycmd
$ scryer-prolog -f --no-add-history consult.pl -g test
```

```trycmd
$ scryer-prolog -f --no-add-history consult_same_file.pl -g test
```

```trycmd
$ scryer-prolog -f --no-add-history consult_update.pl -g test
```

```trycmd
$ scryer-prolog -f --no-add-history consult_dynamic.pl -g test
```

TODO: a bigger issue is that dynamic terms are not cleaned up once a file having their definition is
updated. Uncomment the test below after that is fixed.

$ scryer-prolog -f --no-add-history consult_dynamic_update.pl -g test

Check that backtracking version works too:

```trycmd
$ scryer-prolog -f --no-add-history retract.pl -g test
0
1
2
4

```