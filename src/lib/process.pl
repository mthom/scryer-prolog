:- module(process, [process_create/3]).

:- use_module(library(error)).
:- use_module(library(iso_ext)).
:- use_module(library(lists), [append/3, member/2]).

process_create(Exe, Args, Options) :- 
    must_be(chars, Exe),
    must_be(list(chars), Args),
    must_be(list, Options),
    check_option(Sin, find_stdio(Sin, stdin, Options), valid_stdio, [std], Stdin),
    check_option(Sout, find_stdio(Sout, stdout, Options), valid_stdio, [std], Stdout),
    check_option(Serr, find_stdio(Serr, stderr, Options), valid_stdio, [std], Stderr),
    check_option(Envs, find_env(Envs, Options), valid_env, [environment, []], EnvVars),
    check_option(P, member(process(P), Options), valid_pid, _, Pid),
    check_option(C, member(cwd(C), Options), valid_cwd, _, Cwd),
    '$process_create'(Exe, Args, Stdin, Stdout, Stderr, EnvVars, Cwd, Pid).


check_option(Template, Goal, Pred, Default, Choice) :- 
    findall(Template, Goal, Solutions),
    check_option_(Solutions, Pred, Default, Choice).
    
check_option_([]        , Pred  , Default   , Default   ) :- call(Pred, Default).
check_option_([Choice]  , Pred  , _         , Choice    ) :- call(Pred, Choice).
check_option_([X1,X2|Xs], _     , _         , _         ) :- throw(error(duplicate_option, process_create/3, [X1, X2 | Xs])).

find_stdio([std], Kind, Options ) :- Elem =.. [Kind, std], member(Elem, Options).
find_stdio([null], Kind, Options ) :- Elem =.. [Kind, null], member(Elem, Options).
find_stdio([pipe, Stream], Kind, Options) :- Elem =.. [Kind, pipe(Stream)], member(Elem, Options).
find_stdio([file, Path], Kind, Options ) :- Elem =.. [Kind, file(Path)], member(Elem, Options).

valid_stdio([std]).
valid_stdio([null]).
valid_stdio([pipe, Stream]) :- must_be(var, Stream).
valid_stdio([file, Path]) :- must_be(chars, Path).

find_env([env, ME], Options) :- member(env(E), Options), maplist(assign_to_list, E, ME).
find_env([environment, ME], Options) :- member(environment(E), Options), maplist(assign_to_list, E, ME).

assign_to_list(N=V, [N,V]).

valid_cwd(Cwd) :- var(Cwd) -> true ; must_be(chars).

valid_env([env, E]) :- valid_env_(E).
valid_env([environment, E]) :- valid_env_(E).

valid_env_([]).
valid_env_([N=V|Es]) :- 
    must_be(chars, N),
    must_be(chars, V),
    valid_env_(Es).

valid_pid(Pid) :- must_be(var, Pid).
