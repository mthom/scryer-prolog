:- module(process, [process_create/3]).

:- use_module(library(error)).
:- use_module(library(iso_ext)).
:- use_module(library(lists), [append/3, member/2, maplist/2, maplist/3, select/3]).

process_create(Exe, Args, Options) :- 
    must_be(chars, Exe),
    must_be(list, Args),
    maplist(must_be(chars), Args),
    must_be(list, Options),
    must_be_known_options([stdin, stdout, stderr, env, environment, pid, cwd], [], Options),
    check_options(
        [
            ([stdin], valid_stdio, stdin(std), stdin(Stdin)),
            ([stdout], valid_stdio, stdout(std), stdout(Stdout)),
            ([stderr], valid_stdio, stderr(std), stderr(Stderr)),
            ([env, environment], valid_env, environment([]), Env),
            ([process], valid_pid, process(_), process(Pid)),
            ([cwd], valid_cwd, cwd("."), cwd(Cwd))
        ],
        Options
    ),
    Stdin =.. Stdin1,
    Stdout =.. Stdout1,
    Stderr =.. Stderr1,
    simplify_env(Env, Env1),
    '$process_create'(Exe, Args, Stdin1, Stdout1, Stderr1, Env1, Cwd, Pid).

must_be_known_options(_, _,  []).
must_be_known_options(Valid, Found, [X|XS]) :-
    X =.. [Option|_],
    (
        member(Option, Found) -> throw(error(duplicate_option, process_create/3, Option)) ;
        member(Option, Valid) -> true ;
        throw(error(invalid_option, process_create/3, Option))
    ),
    must_be_known_options(Valid, [Option | Found], XS).

check_options([], _).
check_options([X | XS], Options) :- 
    (Kinds, Pred, Default, Choice) = X,
    findall(P, find_option(Kinds, P, Options), Solutions),
    (
        Solutions = [] -> Choice = Default;
        Solutions = [Provided] -> call(Pred, Provided), Choice = Provided ;
        throw(error(duplicate_option, process_create/3, Solutions))
    ),
    check_options(XS, Options).

find_option([Kind|_], Found, Options) :- Found =.. [Kind,_], member(Found, Options).
find_option([_|Kinds], Found, Options) :- find_option(Kinds, Found, Options).

valid_stdio(IO) :- IO =.. [_, Arg], 
    (
        valid_stdio_(Arg) -> true ;
        throw(error(invalid_stdio, process_create/3, Arg))
    ).

valid_stdio_(std).
valid_stdio_(null).
valid_stdio_(pipe(Stream)) :- must_be(var, Stream).
valid_stdio_(file(Path)) :- must_be(chars, Path).

valid_env(env(E)) :- valid_env_(E).
valid_env(environment(E)) :- valid_env_(E).

valid_env_([]).
valid_env_([E| ES]) :- 
    (
        E =.. [=, N, V] -> true ;
        throw(error(invalid_env_entry, process_create/3, E))
    ),
    must_be(chars, N), 
    must_be(chars, V),
    valid_env_(ES).

valid_pid(pid(Pid)) :- must_be(var, Pid).
valid_cwd(cwd(Cwd)) :- must_be(chars, Cwd).

simplify_env(E, [Kind, Envs1]) :- E =.. [Kind, Envs], simplify_env_(Envs, Envs1).

simplify_env_([],[]).
simplify_env_([N=V|E],[[N, V]|E1]) :- simplify_env_(E, E1).
