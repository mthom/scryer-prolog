:- module(interfaces, []).
:- use_module(library(format)).
:- use_module(library(pio)).

warn(Format, Vars) :-
    warn(user_error, Format, Vars).
warn(Stream, Format, Vars) :-
    prolog_load_context(file, File),
    prolog_load_context(term_position, position_and_lines_read(_,Line)),
    phrase_to_stream(
        (
            "% Warning: ", format_(Format,Vars), format_(" at line ~d of ~a~n",[Line,File])
        ),
        Stream
    ).


user:term_expansion((H :- 0), interface(H)) :-
    predicate_property(H, multifile).

user:term_expansion((M:H :- B), _) :-
    nonvar(B),
    B \= 0,
    \+ M:interface(H),
    functor(H, F, A),
    functor(J, F, A),
    findall(J, M:interface(J), [Jh|Js]),
    warn("Head ~q doesn\'t unify with any of ~q", [H, [Jh|Js]]),
    false.
