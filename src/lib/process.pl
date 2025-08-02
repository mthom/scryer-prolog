:- module(process, [
    process_create/3, 
    process_id/2,
    process_release/1, 
    process_wait/2, 
    process_wait/3, 
    process_kill/1
]).

:- use_module(library(error)).
:- use_module(library(iso_ext)).
:- use_module(library(lists), [member/2, maplist/2, maplist/3, append/2]).
:- use_module(library(reif), [tfilter/3, memberd_t/3]).


%% process_create(+Exe, +Args:list, +Options).
%
% Create a new process by executing the executable Exe and passing it the Arguments Args.
%
% Note: On windows please take note of [windows argument splitting](https://doc.rust-lang.org/std/process/index.html#windows-argument-splitting).
% 
% Options is a list consisting of the following options:
%
%  * `cwd(+Path)`           Set the processes working directory to `Path`
%  * `process(-Process)`    `Process` will be assigned a process handle for the spawned process
%  * `env(+List)`           Don't inherit environment variables and set the variables defined in `List`
%  * `environment(+List)`   Inherit environment variables and set/override the variables defined in `List`
%  * `stdin(Spec)`, `stdout(Spec)` or `stderr(Spec)` defines how to redirect the spawned processes io streams
%
%  The elements of `List` in `env(List)`/`environment(List)` List must be string pairs using `=/2`.
%  `env/1` and `environment/1` may not be both specified.
%
%  The following stdio `Spec` are available:
%  
%  * `std`          inherit the current processes original stdio streams (does currently not account for stdio being changed by `set_input` or `set_output`)
%  * `file(+Path)`  attach the strea to the file at `Path`
%  * `null`         discards writes and behaves as eof for read. Equivalent to using `file(/dev/null)`
%  * `pipe(-Steam)` create a new pipe and assigne one end to the created process and the other end to `Stream`
%
% Specifying an option multiple times is an error, when an option is not specified the following defaults apply:
%
% - `cwd(".")`
% - `environment([])`
% - `stdin(std)`, `stdout(std)`, `stderr(std)`
%
process_create(Exe, Args, Options) :- call_with_error_context(process_create_(Exe, Args, Options), predicate-process_create/3).

process_create_(Exe, Args, Options) :-
    must_be(chars, Exe),
    must_be(list, Args),
    maplist(must_be(chars), Args),
    must_be(list, Options),
    check_options(
        [
            option([stdin], valid_stdio, stdin(std), stdin(Stdin)),
            option([stdout], valid_stdio, stdout(std), stdout(Stdout)),
            option([stderr], valid_stdio, stderr(std), stderr(Stderr)),
            option([env, environment], valid_env, environment([]), Env),
            option([process], valid_uninit_process, process(_), process(Process)),
            option([cwd], valid_cwd, cwd("."), cwd(Cwd))
        ],
        Options,
        process_create_option
    ),
    Stdin =.. Stdin1,
    Stdout =.. Stdout1,
    Stderr =.. Stderr1,
    simplify_env(Env, Env1),
    '$process_create'(Exe, Args, Stdin1, Stdout1, Stderr1, Env1, Cwd, Process).

%% process_id(+Process, -Pid).
%
process_id(Process, Pid) :- call_with_error_context(process_id_(Process, Pid), predicate-process_id/2).

process_id_(Process, Pid) :-
    valid_process(Process),
    must_be(var, Pid),
    '$process_id'(Process, Pid).

%% process_wait(+Process, Status).
%
% See `process_create/3` with `Options = []`
%
process_wait(Process, Status) :- call_with_error_context(process_wait(Process, Status, []), predicate-process_wait/2).


%% process_wait(+Process, Status, Options).
%
% Wait for the process behind the process handle `Process` to exit.
%
% When the process exits regulary `Status` will be unified with `exit(Exit)` where `Exit` is the processes exit code.
% When the process exits was killed `Status` will be unified with `killed(Signal)` where `Signal` is the signal number that killed the process.
% When the process doesn't exit before the timeout `Status` will be unified with `timeout`.
%
% `Options` is a a list of the following options
%
%  * timeout(Timeout) supported values for `Timeout` are 0 or `infinite`
%
% Each options may be specified at most once, when an option is not specified the following defaults apply:
%
% - timeout(infinite)
%
process_wait(Process, Status, Options) :- call_with_error_context(process_wait_(Process, Status, Options), predicate-process_wait/3).

process_wait_(Process, Status, Options) :- 
    valid_process(Process),
    check_options(
        [
            option([timeout], valid_timeout, timeout(infinite), timeout(Timeout))
        ],
        Options,
        process_wait_option
    ),
    '$process_wait'(Process, Exit, Timeout),
    Exit = Status.

valid_timeout(timeout(infinite)).
valid_timeout(timeout(0)).


%% process_kill(+Process).
%
% Kill the process using the process handle `Process`.
% On Unix this sends SIGKILL.
%
% Only works for processes spawned with `process_create/3` that have not yet been release with `process_release/1`
% 
process_kill(Process) :- call_with_error_context(process_kill_(Process), predicate-process_kill/1).

process_kill_(Process) :- 
    valid_process(Process),
    '$process_kill'(Process).

%% process_release(+Process)
%
% wait for the process to exit (if not already) and release process handle `Process`
%
% It's an error if `Process` is not a valid process handle
%
process_release(Process) :- call_with_error_context(process_release_(Process), predicate-process_release/1).

process_release_(Process) :- 
    valid_process(Process),
    process_wait(Process, _),
    '$process_release'(Process).


must_be_known_options(Valid, Options, Domain) :- call_with_error_context(must_be_known_options_(Valid, [], Options, Domain),predicate-must_be_known_options/3).

must_be_known_options_(_, _,  [], _).
must_be_known_options_(Valid, Found, [X|XS], Domain) :-
    ( functor(X, Option, 1) -> true
    ; domain_error(Domain, X, [])
    ) ,
    ( member(Option, Found) -> domain_error(non_duplicate_options, Option , [])
    ; member(Option, Valid) -> true 
    ; domain_error(Domain, Option, [])
    ),
    must_be_known_options_(Valid, [Option | Found], XS, Domain).

check_options(KnownOptions, Options, Domain) :- call_with_error_context(check_options_(KnownOptions, Options, Domain), predicate-check_options/3).

check_options_(KnownOptions, Options, Domain) :-
    maplist(option_names, KnownOptions, Namess),
    append(Namess, Names),
    must_be_known_options(Names, Options, Domain),
    extract_options(KnownOptions, Options).

option_names(option(Names,_,_,_), Names).

extract_options(KnownOptions, Options) :- call_with_error_context(extract_options_(KnownOptions, Options), predicate-extract_options/2).

extract_options_([], _).
extract_options_([X | XS], Options) :- 
    option(Kinds, Pred, Default, Choice) = X,
    tfilter(find_option(Kinds), Options, Solutions),
    ( Solutions = [] -> Choice = Default
    ; Solutions = [Provided] -> functor(Pred, Name, Arity), ArityP1 is Arity+1, call_with_error_context(call(Pred, Provided),predicate-Name/ArityP1), Choice = Provided 
    ; domain_error(non_conflicting_options, Solutions, [])
    ),
    extract_options_(XS, Options).

find_option(Names, Found, T) :- 
    functor(Found, Name, 1), 
    memberd_t(Name, Names, T).

valid_stdio(IO) :- arg(1, IO, Arg), 
    ( var(Arg) -> instantiation_error([]) 
    ; valid_stdio_(Arg) -> true 
    ; domain_error(stdio_spec, Arg, [])
    ).

valid_stdio_(std).
valid_stdio_(null).
valid_stdio_(pipe(Stream)) :- must_be(var, Stream).
valid_stdio_(file(Path)) :- must_be(chars, Path).

valid_env(env(E)) :- 
    must_be(list, E),
    ( valid_env_(E) -> true 
    ; domain_error(process_create_option, env(E), [])
    ).
valid_env(environment(E)) :- 
    must_be(list, E),
    ( valid_env_(E) -> true 
    ; domain_error(process_create_option, environment(E), [])
    ).

valid_env_([]).
valid_env_([N=V|ES]) :- 
    must_be(chars, N), 
    must_be(chars, V),
    valid_env_(ES).

valid_uninit_process(process(Process)) :- must_be(var, Process).

valid_process(Process) :- var(Process) -> instantiation_error([]) ; true.

valid_cwd(cwd(Cwd)) :- must_be(chars, Cwd).

simplify_env(E, [Kind, Envs1]) :- E =.. [Kind, Envs], simplify_env_(Envs, Envs1).

simplify_env_([],[]).
simplify_env_([N=V|E],[[N, V]|E1]) :- simplify_env_(E, E1).
