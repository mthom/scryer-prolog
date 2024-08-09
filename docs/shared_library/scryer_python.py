import contextlib
import ctypes
import json
import os
import platform

install_location = os.getenv("SCRYER_HOME")  # wherever you installed scryer

if platform.system() == 'Linux':
    shared_library_name = 'libscryer_prolog.so'
elif platform.system() == 'Windows':
    shared_library_name = 'scryer_prolog.dll'
elif platform.system() == 'Darwin':
    shared_library_name = 'libscryer_prolog.dylib'

shared_library_path = os.path.join(install_location, 'target', 'release', shared_library_name)

# How to allocate shared library in python and assign correct types to the functions,
# adapt for your language of choice.

lib = ctypes.cdll.LoadLibrary(shared_library_path)

QUERY_STATE_PTR = MACHINE_PTR = ctypes.POINTER(ctypes.c_void_p)
UTF8_BYTES = ctypes.c_char_p
SCRYER_UTF8_PTR = ctypes.POINTER(ctypes.c_char)

lib.scryer_run_query.argtypes = (MACHINE_PTR, UTF8_BYTES,)
lib.scryer_run_query.restype = SCRYER_UTF8_PTR

lib.scryer_free_c_string.argtypes = (SCRYER_UTF8_PTR,)
lib.scryer_free_c_string.restype = None

lib.scryer_machine_new.argtypes = []
lib.scryer_machine_new.restype = MACHINE_PTR

lib.scryer_machine_free.argtypes = (MACHINE_PTR,)
lib.scryer_machine_free.restype = None

lib.scryer_consult_module_string.argtypes = (MACHINE_PTR, UTF8_BYTES)
lib.scryer_consult_module_string.restype = SCRYER_UTF8_PTR

lib.scryer_load_module_string.argtypes = (MACHINE_PTR, UTF8_BYTES,)
lib.scryer_load_module_string.restype = SCRYER_UTF8_PTR

lib.scryer_start_new_query_generator.argtypes = (MACHINE_PTR, UTF8_BYTES,)
lib.scryer_start_new_query_generator.restype = QUERY_STATE_PTR

lib.scryer_cleanup_query_generator.argtypes = (MACHINE_PTR, QUERY_STATE_PTR)
lib.scryer_cleanup_query_generator.restype = SCRYER_UTF8_PTR

lib.scryer_run_query_generator.argtypes = (MACHINE_PTR, QUERY_STATE_PTR)
lib.scryer_run_query_generator.restype = SCRYER_UTF8_PTR


class ScryerPanicException(RuntimeError):
    pass


class ScryerError(Exception):
    pass


def handle_scryer_result(result: str):
    """
    Handle the result returned by the Scryer API.

    :param result: The result returned by the Scryer API.
    :type result: str
    :return: The result if the status is "ok", or True if the result is missing.
    :rtype: Any
    :raise ScryerError: If the status is "error".
    :raise ScryerPanicException: If the status is "panic".
    """
    result = json.loads(result)
    if result["status"] == "ok":
        return result["result"] if 'result' in result else True
    elif result["status"] == "error":
        raise ScryerError(result["error"])
    elif result["status"] == "panic":
        raise ScryerPanicException()


def eval_and_free(machine: MACHINE_PTR, query: str):
    """
    Evaluate the given query on the specified machine and free the allocated memory.

    :param machine: A pointer to the machine object.
    :param query: The query string to be evaluated.
    :return: The result of the query evaluation.
    """
    res_ptr = lib.scryer_run_query(machine, query.encode('utf-8'))
    res = ctypes.cast(res_ptr, UTF8_BYTES).value.decode('utf-8')
    lib.scryer_free_c_string(res_ptr)
    return handle_scryer_result(res)


def run_generator_step(machine: MACHINE_PTR, qs: QUERY_STATE_PTR):
    """
    This method runs a query generator on the given machine and query state. It returns the result of running the generator as a string.

    :param machine: A pointer to the machine object.
    :param qs: A pointer to the query state object.
    :return: The result of running the query generator as a string.
    """
    res_ptr = lib.scryer_run_query_generator(machine, qs)
    res = ctypes.cast(res_ptr, UTF8_BYTES).value.decode('utf-8')
    lib.scryer_free_c_string(res_ptr)
    return handle_scryer_result(res)


def handle_loader_deloader(ptr):
    """
    Deal with functions which have no return value, such as resource deallocators. This will
    throw an error if there was an error.

    :param ptr: A pointer to a memory location
    :return: The result of handling the scryer result

    """
    res = ctypes.cast(ptr, UTF8_BYTES).value.decode('utf-8')
    try:
        return handle_scryer_result(res)
    finally:
        lib.scryer_free_c_string(ptr)


@contextlib.contextmanager
def query_generator(machine: MACHINE_PTR, query: str):
    """
    Generates a query generator for a given machine and query.

    :param machine: A pointer to the machine.
    :param query: The query string.
    :return: A generator that yields the results of running the generator step.
    """
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


def load_facts(machine: MACHINE_PTR, facts: str):
    """
    Load Prolog facts into the specified Scryer machine.

    :param machine: A pointer to the machine object where the facts will be loaded.
    :param facts: A string containing the facts to be loaded.
    :return: None

    """
    handle_loader_deloader(lib.scryer_load_module_string(machine, facts.encode('utf-8')))


def consult(machine: MACHINE_PTR, facts: str):
    """
    Consults the given facts in the specified machine. Effectively the same as `load_facts()`.

    :param machine: Pointer to the machine object.
    :type machine: MACHINE_PTR
    :param facts: The facts to be consulted.
    :type facts: str
    :return: The result of consulting the facts.
    """
    handle_loader_deloader(lib.scryer_consult_module_string(machine, facts.encode('utf-8')))


class ScryerMachine:
    def __init__(self, source=None):
        """
        Constructor for the class.

        :param source: The source of the object.
        :type source: Any, optional
        """
        self.source = source
        self.m: MACHINE_PTR = None

    def __enter__(self, query: str = None):
        """
        Enter method for context manager.

        :param query: Optional query string to be evaluated.
        :return: If query is provided, return the lazy evaluation of the query using the scryer machine.
                 Otherwise, return self.
        """
        self.m = lib.scryer_machine_new()
        if self.source:
            load_facts(self.m, self.source)
        if query:
            return self.lazy_eval(self.m, query)
        return self

    def __exit__(self, *_):
        """
        :param _: any additional arguments passed to the method (not used)
        :return: None

        The method is responsible for freeing the resources held by the Scryer machine, indicated by the `self.m` attribute.

        Example usage:
            with ScryerMachine(source_code) as wam:
                for fact in wam.lazy_eval(some_query):
                    print(fact)

        """
        lib.scryer_machine_free(self.m)

    def lazy_eval(self, query):
        """
        Generator function that lazily evaluates the given query.

        :param query: The query string used to generate the answers.
        :type query: str
        :return: A generator that yields the answers.
        :rtype: generator
        """
        with query_generator(self.m, query) as g:
            for answer in g:
                yield answer

    def consult(self, facts):
        """
        Consults the given facts and loads them into the 'm' object.

        :param facts: A list of facts to consult. Each fact should be a string.
        :type facts: list[str]
        :return: None
        """
        load_facts(self.m, facts)

    def eval(self, fact):
        """
        Greedily evaluates the given query. NOTE: will cause threadlock on infinite query.

        :param query: The query string used to generate the answers.
        :type query: str
        :return: result object
        :rtype: dict
        """

        return eval_and_free(self.m, fact)


if __name__ == '__main__':
    source = '''
    fact(0).
    fact(1).
    fact(2).
    '''
    source1 = '''
    :- use_module(library(dcgs)).
    as --> [].
    as --> [a], as.
    '''
    with ScryerMachine(source) as wam:
        print('?- fact(1). % boolean example')
        for fact in wam.lazy_eval('fact(1).'):
            print(fact)
    # True

    with ScryerMachine(":- use_module(library(dif)). "
                       ":- use_module(library(lists)).") as wam:
        print("% Limitations -- these are INCORRECT!")
        print('?- member(X, [a,"a",f(a),"f(a)",Y,"Y"]) ; dif(X,a), dif(Y,X).')

        for goal in wam.lazy_eval('member(X, [a,"a",f(a),"f(a)",Y,"Y"]) ; dif(X,a), dif(Y,X).'):
            print(goal)
    # {'X': 'a'}
    # {'X': 'a'}
    # {'X': 'f(a)'}
    # {'X': 'f(a)'}
    # {'Y': 'X'}
    # {'X': 'Y'}
    # {'X': '_150', 'Y': '_180'}

    with ScryerMachine("""
    :- use_module(library(dcgs)).
    :- use_module(library(lists)).
    :- use_module(library(clpz)).

    as --> [].
    as --> [a], as.
    """) as wam:
        print('?- phrase(as, As).')
        for n, answer in zip(range(10), wam.lazy_eval('phrase(as, As).')):
            print(n, answer)
    # 0 {'As': ['']}
    # 1 {'As': 'a'}
    # 2 {'As': 'aa'}
    # 3 {'As': 'aaa'}
    # 4 {'As': 'aaaa'}
    # 5 {'As': 'aaaaa'}
    # 6 {'As': 'aaaaaa'}
    # 7 {'As': 'aaaaaaa'}
    # 8 {'As': 'aaaaaaaa'}
    # 9 {'As': 'aaaaaaaaa'}

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
