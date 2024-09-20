import contextlib
import ctypes
import json
import os
import platform
from typing import TypedDict, Union, List, Literal, Dict, ContextManager, Generator


#######################
## Type Declarations ##
#######################

# Not necessary in Python, but to assist with
# readability and intent of functions

class OkListResult(TypedDict):
    status: Literal["ok"]
    result: List[Dict[str, str]]


class OkBoolResult(TypedDict):
    status: Literal["ok"]
    result: bool


class ErrorResult(TypedDict):
    status: Literal["error"]
    error: str


class PanicResult(TypedDict):
    status: Literal["panic"]
    error: Literal["panic"]


SCRYER_QUERY_RESULT = Union[OkListResult, OkBoolResult, ErrorResult, PanicResult]

# wherever you installed Scryer Prolog.
# if you are just hacking, feel free to replace this with
# hard coded path to your installation location
install_location = os.getenv("SCRYER_HOME")

if platform.system() == 'Linux':
    shared_library_name = 'libscryer_prolog.so'
elif platform.system() == 'Windows':
    shared_library_name = 'scryer_prolog.dll'
elif platform.system() == 'Darwin':
    shared_library_name = 'libscryer_prolog.dylib'
else:
    raise RuntimeError("""Unsupported operating system, maybe! If
    you know what you are doing, comment this out and put the name of the shared library here
    and modify the `shared_library_path` below as required!""")

# replace 'release' with 'debug' if you are developing the bindings
# compile the code with `cargo build --lib` for 'debug'
# compile the code with `cargo build --release` for speed in production.
shared_library_path = os.path.join(install_location, 'target', 'debug', shared_library_name)

########################
## LOW LEVEL BINDINGS ##
########################

# How to allocate shared library in python and assign correct types to the functions,
# adapt for your language of choice. Please refer to the scryer prolog documentation
# and corresponding C header for more information.
#
# Please see the higher level abstractions below for intended use. These are
# not intended for general use because it's quite inconvenient to serialize to bytes,
# deserialize, check for null pointers, etc. There's also significant risk of resource leaks
# and extra bookkeeping that would be required.
#
# Note: the wrapper functions over the low level DLL are not strictly necessary but
# help with autocompletion.

lib = ctypes.cdll.LoadLibrary(shared_library_path)

QUERY_STATE_PTR = MACHINE_PTR = ctypes.POINTER(ctypes.c_void_p)
UTF8_BYTES = ctypes.c_char_p
SCRYER_UTF8_PTR = ctypes.POINTER(ctypes.c_char)
INT32 = ctypes.c_int32

lib.scryer_run_query.argtypes = [MACHINE_PTR, UTF8_BYTES]
lib.scryer_run_query.restype = SCRYER_UTF8_PTR


def scryer_run_query(machine_ptr: MACHINE_PTR, utf8_bytes: bytes) -> SCRYER_UTF8_PTR:
    return lib.scryer_run_query(machine_ptr, utf8_bytes)


lib.scryer_free_c_string.argtypes = [SCRYER_UTF8_PTR]
lib.scryer_free_c_string.restype = None


def scryer_free_c_string(utf8_ptr: UTF8_BYTES):
    return lib.scryer_free_c_string(utf8_ptr)


lib.scryer_machine_new.argtypes = []
lib.scryer_machine_new.restype = MACHINE_PTR


def scryer_machine_new():
    return lib.scryer_machine_new()


lib.scryer_machine_free.argtypes = [MACHINE_PTR]
lib.scryer_machine_free.restype = None


def scryer_machine_free(machine_ptr: MACHINE_PTR) -> SCRYER_UTF8_PTR:
    return lib.scryer_machine_free(machine_ptr)


lib.scryer_consult_module_string.argtypes = [MACHINE_PTR, UTF8_BYTES, UTF8_BYTES]
lib.scryer_consult_module_string.restype = INT32


def scryer_consult_module_string(machine_ptr: MACHINE_PTR, module_name: bytes, facts: bytes):
    return lib.scryer_consult_module_string(machine_ptr, module_name, facts)


lib.scryer_run_query_iter.argtypes = [MACHINE_PTR, UTF8_BYTES]
lib.scryer_run_query_iter.restype = QUERY_STATE_PTR


def scryer_run_query_iter(machine_ptr: MACHINE_PTR, query: bytes) -> QUERY_STATE_PTR:
    return lib.scryer_run_query_iter(machine_ptr, query)


lib.scryer_query_state_free.argtypes = [QUERY_STATE_PTR]
lib.scryer_query_state_free.restype = INT32


def scryer_query_state_free(query_state_ptr: QUERY_STATE_PTR):
    return lib.scryer_query_state_free(query_state_ptr)


lib.scryer_run_query_next.argtypes = [QUERY_STATE_PTR]
lib.scryer_run_query_next.restype = SCRYER_UTF8_PTR


def scryer_run_query_next(query_state_ptr: QUERY_STATE_PTR) -> SCRYER_UTF8_PTR:
    return lib.scryer_run_query_next(query_state_ptr)


######################
## HELPER FUNCTIONS ##
######################

# If programming in a purely functional style, the following functions would be sufficient.
# However, using these functions alone would be very prone to resource leaks and confusion
# from leaky abstractions that arise from the fact that Scryer Prolog (like most Prologs)
# was not designed to be used as a shared library in procedural languages.
#
# You would need to understand that the underlying VM (the Warren Abstract Machine) is only
# configured to be in one "mode" at a time. If it is currently serving a lazy query,
# it cannot do any other actions until it deallocates the resources for that query
# and returns to standby mode. As such, you would need to track the pointer for
# the query state that would be used to deallocate the lazy query mode.
#
# The `query_generator` context manager cleans up resources automatically
# but does not ensure that multiple queries are not running simultaneously.


class ScryerPanicException(RuntimeError):
    pass


class ScryerError(Exception):
    pass


def handle_scryer_result(result: str) -> SCRYER_QUERY_RESULT:
    result = json.loads(result)
    if result["status"] == "ok":
        return result["result"] if 'result' in result else True
    elif result["status"] == "error":
        raise ScryerError(result["error"])
    elif result["status"] == "panic":
        raise ScryerPanicException()


def eval_and_free(machine: MACHINE_PTR, query: str) -> SCRYER_QUERY_RESULT:
    res_ptr = scryer_run_query(machine, query.encode('utf-8'))
    res = ctypes.cast(res_ptr, UTF8_BYTES).value.decode('utf-8')
    scryer_free_c_string(res_ptr)
    return handle_scryer_result(res)


def run_generator_step(qs: QUERY_STATE_PTR) -> SCRYER_QUERY_RESULT | None:
    res_ptr = scryer_run_query_next(qs)
    if not res_ptr or res_ptr.contents is None:
        return None
    res = ctypes.cast(res_ptr, UTF8_BYTES).value.decode('utf-8')
    scryer_free_c_string(res_ptr)
    return handle_scryer_result(res)


def handle_loader_deloader(ret_val: INT32, message: str = None):
    """
    Deal with functions which have no return value, such as resource deallocators. This will
    throw an error if there was an error.

    :param ret_val: A pointer to a memory location
    :return: The result of handling the Scryer result
    """
    if ret_val == 1:
        raise ScryerError(message) if message else ScryerError()


@contextlib.contextmanager
def query_generator(machine: MACHINE_PTR, query: str) -> ContextManager[Generator[SCRYER_QUERY_RESULT, None, None]]:
    """
    Generates a query generator for a given machine and query.

    :param machine: A pointer to the machine.
    :param query: The query string.
    :return: A generator that yields the results of running the generator step.
    """
    qs: QUERY_STATE_PTR = scryer_run_query_iter(machine, query.encode('utf-8'))
    deloaded = False
    try:
        def g():
            nonlocal deloaded
            while True:
                answer = run_generator_step(qs)
                if answer is None:
                    handle_loader_deloader(scryer_query_state_free(qs))
                    deloaded = True
                    break
                yield answer[0] if isinstance(answer, list) else answer

        yield g()
    finally:
        if deloaded is False:
            handle_loader_deloader(scryer_query_state_free(qs))


def consult(machine: MACHINE_PTR, facts: str, module_name: str = None):
    """
    Consults the given facts in the specified machine. Effectively the same as `load_facts()`.

    :param module_name: name of module to install facts, optional
    :param machine: Pointer to the machine object.
    :type machine: MACHINE_PTR
    :param facts: The facts to be consulted.
    :type facts: str
    :return: The result of consulting the facts.
    """
    if module_name and isinstance(module_name, str):
        facts, module_name = module_name, facts
    else:
        module_name = 'facts'
    handle_loader_deloader(scryer_consult_module_string(machine, module_name.encode('UTF-8'), facts.encode('utf-8')))


####################
## SCRYER MACHINE ##
####################

## This is a suggested high level API that prevents most footguns as long as you stay within the context manager API.
## see examples below for intended usage and example queries.
## For more information on using Scryer Prolog, check out https://www.metalevel.at/prolog and
## https://www.youtube.com/@ThePowerOfProlog
class ScryerMachine:
    class IllegalWAMStateError(RuntimeError):
        pass

    def __init__(self, source=None):
        """
        Constructor for the class.

        :param source: The source of the object.
        :type source: Any, optional
        """
        self.source = source
        self.m: MACHINE_PTR = None
        self.query_in_progress = False

    def __enter__(self, query: str = None):
        """
        Enter method for context manager.

        :param query: Optional query string to be evaluated.
        :return: If query is provided, return the lazy evaluation of the query using the scryer machine.
                 Otherwise, return self.
        """
        self.m = scryer_machine_new()
        if self.source:
            self.consult(self.source)
        if query:
            return self.lazy_eval_context(query)
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
        scryer_machine_free(self.m)

    def lazy_eval_context(self, query: str) -> ContextManager[Generator[SCRYER_QUERY_RESULT, None, None]]:
        """
        Context manager yielding generator function that lazily evaluates the given query.

        :param query: The query string used to generate the answers.
        :type query: str
        :return: A context manager yielding a generator that yields the answers.
        """
        self._valid_query_state_check()
        self.query_in_progress = True
        try:
            return query_generator(self.m, query)
        finally:
            self.query_in_progress = False

    def _valid_query_state_check(self):
        if self.query_in_progress is True:
            raise ScryerMachine.IllegalWAMStateError(
                "Query already running, must finish this query before starting a new one!"
            )

    def consult(self, facts: str):
        """
        Consults the given facts and loads them into the 'm' object.

        :param facts: A list of facts to consult. Each fact should be a string.
        :type facts: list[str]
        :return: None
        """
        self._valid_query_state_check()
        consult(self.m, facts)

    def eval(self, query: str):
        """
        Greedily evaluates the given query. NOTE: will cause threadlock on infinite query.

        :param query: The query string used to generate the answers.
        :type query: str
        :return: result object
        :rtype: dict
        """
        self._valid_query_state_check()
        return eval_and_free(self.m, query)


if __name__ == '__main__':


    with ScryerMachine(":- use_module(library(dif)). "
                       ":- use_module(library(lists)).") as wam:
        with wam.lazy_eval_context('member(X, [a,"a",f(a),"f(a)",Y,"Y", true, "true", false, "false"]).') as query:
            for goal in query:
                print(goal)

    # # {'X': 'a'}
    # # {'X': 'a'}
    # # {'X': 'f(a)'}
    # # {'X': 'f(a)'}
    # # {'Y': 'X'}
    # # {'X': 'Y'}
    # # {'X': '_150', 'Y': '_180'}

    with ScryerMachine("""
    :- use_module(library(dcgs)).
    :- use_module(library(lists)).
    :- use_module(library(clpz)).

    as --> [].
    as --> [a], as.
    """) as wam:
        print('?- phrase(as, As).')
        with wam.lazy_eval_context('phrase(as, As).') as query:
            for n, answer in zip(range(10), query):
                print(n, answer)

    # # 0 {'As': ['']}
    # # 1 {'As': 'a'}
    # # 2 {'As': 'aa'}
    # # 3 {'As': 'aaa'}
    # # 4 {'As': 'aaaa'}
    # # 5 {'As': 'aaaaa'}
    # # 6 {'As': 'aaaaaa'}
    # # 7 {'As': 'aaaaaaa'}
    # # 8 {'As': 'aaaaaaaa'}
    # # 9 {'As': 'aaaaaaaaa'}
    #
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
            with wam.lazy_eval_context('phrase(as, As).') as query1:
                for n, a in zip(range(3), query1):
                    with wam1.lazy_eval_context('fact(Fact).') as query2:
                        for i, fact in zip(range(3), query2):
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

