# Builtin predicates should be visible

```trycmd
$ scryer-prolog -f --no-add-history -g 'current_predicate(true/0), write(ok); write(fail).'
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
$ echo "a :- b.\na1 :- b(1)." > issue_3070_test_tmp.pl; scryer-prolog -f --no-add-history -g 'consult(issue_3070_test_tmp), current_predicate(a/0), current_predicate(a1/0), \+ current_predicate(b/0), \+ current_predicate(b/1), write(ok); write(fail).'; rm issue_3070_test_tmp.pl
ok
```