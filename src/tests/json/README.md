## Benchmarks

These are honestly super flawed (single read/write of a single file) but that can at least capture movement on the 
order of 0.1 s, and that's good enough for me.

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

After making the code more general:
```
?- test_json:test_json_read.
   % CPU time: 0.217 seconds
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

After making the code more general:
```
?- test_json:test_json_minify.
   % CPU time: 0.013 seconds
```
