## Benchmarks

### Read

With CLP(Z):

```
?- test_json:test_json_read.
   % CPU time: 41.522 seconds
```

After removing CLP(Z):

```
?- test_json:test_json_read.
   % CPU time: 0.444 seconds
```

With first argument indexing optimizations:
```
?- test_json:test_json_read.
   % CPU time: 0.310 seconds
```

### Write

Without first argument indexing optimizations:
```
?- test_json:test_json_minify.
   % CPU time: 0.014 seconds
```

With first argument indexing optimizations:

```
?- test_json:test_json_minify.
   % CPU time: 0.015 seconds
```
