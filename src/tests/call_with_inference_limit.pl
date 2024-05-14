:- module(tests_on_call_with_inference_limit, []).

:- use_module(library(lists)).
:- use_module(library(iso_ext)).

:- dynamic(f/1).
:- dynamic(g/1).

test_queries_on_call_with_inference_limit :-
    catch(call_with_inference_limit(throw(error), 0, inference_limit_exceeded),
	  error,
	  true),
    catch(call_with_inference_limit(throw(error), 1, inference_limit_exceeded),
	  error,
	  true),
    \+ call_with_inference_limit(g(X), 5, R),
    maplist(assertz, [g(1), g(2), g(3), g(4), g(5)]),
    findall([R,X],
	    call_with_inference_limit(g(X), 11, R),
	    [[true, 1],
	     [true, 2],
	     [true, 3],
	     [true, 4],
	     [!, 5]]),
    findall([R,X],
	    (call_with_inference_limit(g(X), 11, R), call(true)),
	    [[true, 1],
	     [true, 2],
	     [true, 3],
	     [true, 4],
	     [!, 5]]),
    findall([R,X],
	    (call_with_inference_limit(g(X), 2, R), call(true)),
	    [[true, 1],
	     [true, 2],
	     [inference_limit_exceeded, _]]),
    findall([X,R1,R2],
	    (call_with_inference_limit(g(X), 5, R1),
	     call_with_inference_limit(g(X), 6, R2)),
	    [[1,true,!],
	     [2,true,!],
	     [3,true,!],
	     [4,true,!],
	     [5,!,!]]),
    \+ \+ assertz((f(X) :- call_with_inference_limit(tests_on_call_with_inference_limit:g(X), 11, _))),
    findall([R,X],
	        call_with_inference_limit(f(X), 14, R),
            Solutions),
	Solutions == [[true,1],
	              [true,2],
	              [true,3],
	              [true,4],
	              [!,5]].

:- initialization(test_queries_on_call_with_inference_limit).
