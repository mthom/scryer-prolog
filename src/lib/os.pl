 /* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Predicates for reasoning about the operating system (OS) environment.
   Written July 2020 by Markus Triska (triska@metalevel.at).

   Lists of characters are used throughout to represent keys and values.

   Example:

       ?- getenv("LANG", Ls).
          Ls = "en_US.UTF-8".

   Public domain code.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- module(os, [getenv/2,
               setenv/2,
               unsetenv/1,
               pid/1]).

:- use_module(library(error)).
:- use_module(library(charsio)).
:- use_module(library(lists)).

getenv(Key, Value) :-
        must_be_env_var(Key),
        '$getenv'(Key, Value).

setenv(Key, Value) :-
        must_be_env_var(Key),
        must_be_chars(Value),
        '$setenv'(Key, Value).

unsetenv(Key) :-
        must_be_env_var(Key),
        '$unsetenv'(Key).

pid(PID) :-
        can_be(integer, PID),
        '$pid'(PID).	

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   For now, we only support a restricted subset of variable names.

   The reason is that Rust may panic if a key is empty, contains an
   ASCII equals sign '=' or the NUL character '\0', or when the value
   contains the NUL character.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

must_be_env_var(Cs) :-
        must_be_chars(Cs),
        Cs = [_|_],
        (   maplist(permitted, Cs) -> true
        ;   domain_error(env_var, Cs, os)
        ).

permitted(C) :- char_type(C, alnum).
permitted(C) :- char_type(C, ascii_punctuation).
permitted('_').

must_be_chars(Cs) :-
        must_be(list, Cs),
        maplist(must_be(character), Cs).
