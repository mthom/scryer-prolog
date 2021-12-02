% Source: https://stackoverflow.com/a/30791637

:- module(debug, [
    op(900, fx, $),
    op(900, fx, $-),
    op(950, fy, *),
    (*)/1,
    ($)/1,
    ($-)/1,
    ($)//1,
    ($-)//1
]).

:- use_module(library(dcgs), [phrase/3]).
:- use_module(library(format), [portray_clause/1]).
:- use_module(library(lambda), [(\)/3,(^)/3,(^)/4]).

:- meta_predicate(*(0)).
:- meta_predicate($(0)).
:- meta_predicate($-(0)).

$-(G_0) :-
   catch(G_0, Ex, ( portray_clause(exception:Ex:G_0), throw(Ex) ) ).

$(G_0) :-
   portray_clause(call:G_0),
   $-G_0,
   portray_clause(exit:G_0).

*(_).

% Equivalent DCG rules
:- meta_predicate($(2, ?, ?)).
:- meta_predicate($-(2, ?, ?)).

$-G_2 --> \Xs0^Xs^
   catch(phrase(G_2, Xs0, Xs), Ex, (
      portray_clause(exception:Ex:G_2=(Xs0, Xs)), throw(Ex)
   )).

$G_2 --> \Xs0^Xs^(
   portray_clause(call:G_2=(Xs0, Xs)),
   phrase($-G_2, Xs0, Xs),
   portray_clause(exit:G_2=(Xs0, Xs))
).
