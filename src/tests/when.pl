/**/

:- module(when_tests, []).

:- use_module(library(when)).

:- use_module(test_framework).

test("condition true before ground/1",(
    A = 1,
    when(ground(A), Run = true),
    Run == true
)).

test("condition true before nonvar/1",(
    A = a(_),
    when(nonvar(A), Run = true),
    Run == true
)).

test("condition true before ','/2",(
    A = 1,
    B = a(_),
    when((ground(A), nonvar(B)), Run = true),
    Run == true
)).

test("condition true before (;)/2",(
    A = 1,
    when((ground(A) ; nonvar(_)), Run1 = true),
    Run1 == true,

    B = a(_),
    when((ground(_) ; nonvar(B)), Run2 = true),
    Run2 == true
)).

test("condition true after ground/1",(
    when(ground(A), Run = true),
    var(Run),
    A = 1,
    Run == true
)).

test("condition true after nonvar/1",(
    when(nonvar(A), Run = true),
    var(Run),
    A = a(_),
    Run == true
)).

test("condition true after ','/2",(
    when((ground(A), nonvar(B)), Run = true),
    var(Run),
    A = 1,
    var(Run),
    B = a(_),
    Run == true
)).

test("condition true after (;)/2",(
    when((ground(A) ; nonvar(_)), Run1 = true),
    var(Run1),
    A = 1,
    Run1 == true,

    when((ground(_) ; nonvar(B)), Run2 = true),
    var(Run2),
    B = a(_),
    Run2 == true
)).

test("multiple when/2 on same variable",(
    when(nonvar(A), Run1 = true),
    when(ground(A), Run2 = true),
    var(Run1), var(Run2),
    A = a(B),
    Run1 == true, var(Run2),
    B = 1,
    Run2 == true
)).
