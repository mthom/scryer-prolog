:- use_module(library(format)).

run :-
    catch(call(foo, 1),_,true),
    current_predicate(foo/1),
    format("~s", ["foo/1 defined"]). % shouldn't happen

run.

:- initialization(run).