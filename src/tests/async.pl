:- module(async_tests, []).
:- use_module(library(cont)).
:- use_module(library(reif)).
:- use_module(library(debug)).
:- use_module(library(async)).
:- use_module(library(clpz)).
:- use_module(library(lists)).
:- use_module(library(lambda)).
:- use_module(library(iso_ext)).
:- use_module(test_framework).

merge_async([Arg|Args]) :-
        bb_get(merge_args, MergeArgs),
        bb_put(merge_args,[Arg|MergeArgs]),
        length(Args, N),
        if_(clpz_t(N #> 0),
            await(async_tests:merge_async(Args)),
            true
           ).
merge_async([]).

target(X) :- shift(X).

aggressive_target(X) :-
        %% inside an internal reset, you are now in a syncronous context until you shift/1 back
        shift(X),
        shift(X),
        await(true).

aggressive_jump(X) :-
        reset(async_tests:aggressive_target(X), X, cont(Cont)),
        reset(Cont,X,cont(C1)),
        C1.

test("can process single async predicate",
        (
         bb_put(merge_args, []),
         async_event_loop([async_tests:merge_async([a,b,c])]),
         bb_get(merge_args, [c,b,a])
         )
       ).

test("can merge two lists asyncronously",
     (
      bb_put(merge_args, []),
      async_event_loop([async_tests:merge_async([a,b,c]),
                           async_tests:merge_async([1,2,3])
                          ]),
      bb_get(merge_args, [3,c,2,b,1,a])
     )
    ).


test("can late bind async",
     (
      async_event_loop([await(X=N), await(M#=1+N), await(X=2)]),
      M=3
     )
    ).


test("async does not interfere with normal shift/reset",
     async_event_loop([reset(async_tests:target(1),1,cont(true))])
    ).

test("async does not interfere with aggressive shift/reset",
     async:async_event_loop([async_tests:aggressive_jump(1)])
    ).

test("nested async loops -- this is madness, but just for stress testing",
     (   async_event_loop([
                           async_event_loop([async_tests:aggressive_jump(42)]),
                           async_tests:aggressive_jump(42),
                           async_event_loop([async_event_loop([async_tests:aggressive_jump(N),
                                                               async_tests:aggressive_jump(M)]),
                                             async_event_loop([async_tests:aggressive_jump(A),
                                                               async_tests:aggressive_jump(B)])])

                           ]),
         N=1,M=2,A=3,B=4,
         42 #= N+M+A+B+32
     )
    ).

% ?- test_framework:main(async_tests).
