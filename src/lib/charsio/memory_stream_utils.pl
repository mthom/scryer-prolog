/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Internal utilities supporting charsio:chars_to_stream/3.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- module(memory_stream_utils, [parse_stream_options_list/2, validate_chars/2]).

:- use_module(library(lists)).
:- use_module(library(error)).


option_default(type, text).
option_default(reposition, false).
option_default(alias, []).
option_default(eof_action, eof_code).

parse_stream_options_list(Options, [Alias, EOFAction, Reposition, Type]) :-
        maplist(parse_option, Options),
        option_default(type, Type, Options),
        option_default(reposition, Reposition, Options),
        option_default(alias, Alias, Options),
        option_default(eof_action, EOFAction, Options).

option_default(Option, Resolved, Options) :-
        option_default(Option, Default),
        MaybeOption =.. [Option,Answer],
        (   member(MaybeOption, Options) ->
            Resolved=Answer
        ;   Resolved=Default
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   ?- option_default(type, Resolved, []).
   ?- option_default(type, Resolved, [type(binary)]).
   ?- option_default(type, Resolved, [type(text)]).
   ?- option_default(type, Resolved, [alias]).
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

parse_option(type(Type)) :-
        (   memberchk(Type, [binary, text]), !
        ;   throw(error(instantiation_error, choose_for(type, one_of(binary, text))))
        ).

parse_option(reposition(Bool)) :-
           catch(must_be(boolean, Bool),
                 error(_,_),
                 throw(error(instantiation_error, choose_for(binary, one_of(true,false))))
                ).

parse_option(alias(A)) :-
        (   var(A)
        ->  throw(error(instantiation_error, must_satisfy(alias, var)))
        ;   true
        ),
        (   atom(A), dif(A, []), !
        ;   throw(error(instantiation_error, must_satisfy(alias, (atom, dif([])))))
        )
        .


parse_option(eof_action(Action)) :-
        (   nonvar(Action), memberchk(Action, [eof_code, error, reset]), !
        ;   throw(error(domain_error(stream_option), choose_one(eof_action, [eof_code, error, reset])))
        ).

validate_chars(Chars, Type) :-
        validate_chars_(Chars, Type).

valid_byte_(Byte) :-
        must_be(integer, Byte),
        Byte >= 0,
        Byte < 256.

validate_chars_(Chars, binary) :-
        maplist(valid_byte_, Chars).

validate_chars_(Chars, text) :-
        must_be(chars, Chars).
