### Using Scryer Prolog as a Shared Library

Think of a shared library like a toolbox filled with pre-built tools (functions) that other programs can use without needing to rebuild everything from scratch. In our case, `libscryer_prolog.XXX` is the toolbox containing Scryer Prolog's powerful logic engine.

If you are familiar with using shared libraries, [`docs/shared_library/libscryer_prolog.h`](./libscryer_prolog.h) file is automatically generated from the latest bindings, please use it as a reference to implement the bindings in the language of your choice.

**Note:** Many of the code examples here will be in Python. This is not an endorsement of a particular language, but used for clarity and accessibility, and due to the shared library author's familiarity. 

See [Scryer Prolog online documentation](https://docs.rs/scryer-prolog/latest/scryer_prolog/) for summary of available functions. 

**Steps to Use the Shared Library:**

1. **Locate the Library:** After building Scryer Prolog, you'll find the shared library in:

   `<PATH-TO>/scryer-prolog/target/release`. 
   
   Replace `<PATH-TO>` with the actual path where you installed Scryer Prolog on your computer. The library will have a name like `libscryer_prolog.so` (Linux), `libscryer_prolog.dylib` (macOS), or `scryer_prolog.dll` (Windows).

2. **Load the Library:**  Here are basic examples for common languages:

   * **C/C++ (Linux/macOS):**
     ```c++
     #include <dlfcn.h>

     void* handle = dlopen("libscryer_prolog.so", RTLD_LAZY); // Load the library
     if (!handle) {
         // Handle error: library not found
     }

     // ... Get function pointers from the loaded library ...
     ```

   * **Python:** You'll typically use libraries like `ctypes`:
      ```python
      import ctypes

      lib = ctypes.cdll("./libscryer_prolog.so") # Replace with correct path

      # ... Access functions in lib ...
      ```
3. **Access Functions:** Once the library is loaded, you can call its functions (like `scryer_consult_module_string`, `scryer_run_query`) just like you would any other function in your code. See the Python reference implementation below.


 **Important Notes:**

* **Memory Management:** Be extra careful about memory management when interacting with C libraries from other languages (especially strings). See below.


The following functions are exposed:

**Shared Library Memory Management Considerations and Usage Overview**


* **Ownership Transfer:**

   The Rust library uses C-style strings (`CString`) to return data. To avoid premature cleanup by Rust's garbage collector, ownership of the string pointer is transferred to the client application. This means the client becomes responsible for freeing the memory using `scryer_free_c_string`. Failure to do so will cause memory leaks.


**Using the Library: A Step-by-Step Guide**

1. **Initialization (`scryer_machine_new`):** Before using any other function, initialize the Prolog machine using `scryer_machine_new`.  This creates a pointer that must be tracked by the client and later released with `scryer_machine_free`.

2. **Loading Data:** You have two options for loading Prolog data:
   * **Direct Consultation:** Use `scryer_consult_module_string` to load and immediately run Prolog source code from a C string. Think of it as directly providing the source code to Scryer Prolog.
   * **Query Generation:**

     - Start a new query generator using  `scryer_start_new_query_generator`, passing your machine pointer from step 1 and a prolog query as input (do not include the `?-` functor).
     - Use `scryer_run_query_generator` repeatedly until it returns `{ "status": "ok", "result": <boolean> }`. This indicates that all results have been generated. To be clear, if the first "result" is True, all results will continue to be True. Once a result returns False, all further results will continue to be False.

3. **Running Queries:**

   * For non-generative queries (those with finite results), use `scryer_run_query`.
   * For potentially infinite result sets, utilize the query generator approach described above.

4. **Cleanup:**

   * Always call `scryer_cleanup_query_generator` after finishing with a query generator to release associated resources (unless it's done internally for you).
   * Call `scryer_machine_free` once you are done using the Prolog machine, regardless of the loading and querying methods used.

5. **Important Caveats and Known Limitations:**

    * The JSON code returned by `scryer_run_query` and `scryer_run_query_generator` returns a Web API-style response, which is NOT in keeping with the general spirit of Prolog to return _goals_ (which would be valid inputs to those same functions). Future APIs will return valid Scryer Prolog goals.
    * The results yielded by `scryer_cleanup_query_generator` do not have _determinism_, meaning, the results are exhausted when the first `boolean` result appears. This will be addressed in future enhancements.
    * Residual goals are **not** expressed correctly by this API, these APIs can only express concrete (equality) goals. The improved APIs in a future release will address this point.
    * A single machine instance can only run a single generative query a time. This is not normally a concern in normal Scryer Prolog operation, but when used as a library, there could be a temptation to generate multiple streams from the same machine, however, this is undefined behavior -- it could cause a panic or incorrect results:
    
```python
if __name__ == '__main__':
    with ScryerMachine("""
    :- use_module(library(dcgs)).
    :- use_module(library(lists)).
    :- use_module(library(clpz)).

    as --> [].
    as --> [a], as.
    
    fact(0).
    fact(1).
    fact(2).
    """) as wam:
        for n, b in zip(range(10), wam.lazy_eval('phrase(bs, Bs).')):
            for i, a in zip(range(10), wam.lazy_eval('fact(Fact).')):
                print(n, i, a, b)

## Expected
# Panic -- bs is not defined.

## Actual 
# 0 0 {'Fact': 0} {'Bs': ['']}
# 0 1 {'Fact': 1} {'Bs': ['']}
# 0 2 {'Fact': 2} {'Bs': ['']}

```

a better approach, for now, would be to use distinct machines for multiple generative streams:

```python
if __name__ == '__main__':
    source = """
        :- use_module(library(dcgs)).
        :- use_module(library(lists)).
        :- use_module(library(clpz)).

        as --> [].
        as --> [a], as.

        fact(0).
        fact(1).
        fact(2).
        """

    with ScryerMachine(source) as wam:
        with ScryerMachine(source) as wam1:
            for n, a in zip(range(3), wam.lazy_eval('phrase(as, As).')):
                for i, fact in zip(range(3), wam1.lazy_eval('fact(Fact).')):
                    print(n, i, fact, a)

# 0 0 {'Fact': 0} {'As': ['']}
# 0 1 {'Fact': 1} {'As': ['']}
# 0 2 {'Fact': 2} {'As': ['']}
# 1 0 {'Fact': 0} {'As': 'a'}
# 1 1 {'Fact': 1} {'As': 'a'}
# 1 2 {'Fact': 2} {'As': 'a'}
# 2 0 {'Fact': 0} {'As': 'aa'}
# 2 1 {'Fact': 1} {'As': 'aa'}
# 2 2 {'Fact': 2} {'As': 'aa'}
                                                        
```

  * Besides being limited to a single generative stream at a time, when the generative stream is finished or not longer needed, the resources used MUST be manually deallocated with `scryer_cleanup_query_generator`, or it will leave the Prolog machine in an indeteriminate state and future answers will not be accurate (if it doesn't cause a kernel panic). I advise you to treat a both scryer machines and generative queries the same way you would treat a file or other resource, and wrap it with a try/finally or other form of context manager, e.g.:
  
```python
# ... snip ...
class ScryerMachine:

    def __init__(self, source=None):
        self.source = source
        self.m: MACHINE_PTR = None

    def __enter__(self, query: str = None):
        self.m = lib.scryer_machine_new() # initiate and store machine pointer
        if self.source:
            load_facts(self.m, self.source)
        if query:
            return self.lazy_eval(self.m, query)
        return self

    def __exit__(self, *_):
        lib.scryer_machine_free(self.m) # deallocate resources when lexical scope ends
        
# ... snip ...
```

```python
# ...snip...

@contextlib.contextmanager
def query_generator(machine: MACHINE_PTR, query: str):
    qs: QUERY_STATE_PTR = lib.scryer_start_new_query_generator(machine, query.encode('utf-8'))
    try:
        def generator():
            seen_answer = False
            while True:
                answer = run_generator_step(machine, qs)
                if not isinstance(answer, list):
                    if seen_answer:
                        break
                    yield answer[0] if isinstance(answer, list) else answer
                    break
                seen_answer = True
                yield answer[0] if isinstance(answer, list) else answer

        yield generator()
    finally:
        handle_loader_deloader(lib.scryer_cleanup_query_generator(machine, qs))
# ...snip...
```

See [`scryer_python.py`](scryer_python.py) for a complete example.
  
  * Note that the JSON printer returns results that are not completely accurate when it comes to differentiating strings from symbols, e.g.:
    
**Correct**
```prolog


    ?- member(X, [a,"a",f(a),"f(a)",Y,"Y"]) ; dif(X,a), dif(Y,X).
    X = a
    ; X = "a"
    ; X = f(a)
    ; X = "f(a)"   % these are correct
    ; X = Y
    ; X = "Y"
    ; dif:dif(X,a), dif:dif(Y,X).
```

**Incorrect**
```python
if __name__ == '__main__':
    with ScryerMachine(":- use_module(library(dif)). "
                       ":- use_module(library(lists)).") as wam:
        for goal in wam.lazy_eval('member(X, [a,"a",f(a),"f(a)",Y,"Y"]) ; dif(X,a), dif(Y,X).'):
            print(goal)
    ## INCORRECT
    # {'X': 'a'}
    # {'X': 'a'}
    # {'X': 'f(a)'}
    # {'X': 'f(a)'}
    # {'Y': 'X'}
    # {'X': 'Y'}
    # {'X': '_150', 'Y': '_180'}
```

This discrepancy will be addressed in future API releases.
