% Source: https://stackoverflow.com/a/30791637

:- module(debug, [
    op(900, fx, $),
    op(900, fx, $-),
    op(950, fy, *),
    (*)/1,
    ($)/1,
    ($-)/1
]).

:- use_module(library(format), [portray_clause/1]).

:- meta_predicate *(0).
:- meta_predicate $(0).
:- meta_predicate $-(0).

$-(G_0) :-
   catch(G_0, Ex, ( portray_clause(exception:Ex:G_0), throw(Ex) ) ).

$(G_0) :-
   portray_clause(call:G_0),
   $-G_0,
   portray_clause(exit:G_0).

*(_).
