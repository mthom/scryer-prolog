/**/

:- module(nth_partial_strings_tests, []).

:- use_module(library(between)).
:- use_module(library(lists)).

:- use_module(test_framework).

test("nth_partial_string_tests#1827_1", (
         L="ab",
         findall([N,E], (between(0,2,N), nth0(N,[x|L],E)), S),
         S = [[0,x],[1,a],[2,b]]
     )).

test("nth_partial_string_tests#2381_1", (
         G="AA",
         G=[_|Gs],
         G_=['A'|Gs],
         write(G_),
         nth0(1,G_,C),
         char_code(C,N),
         write(N),
         nl
     )).

test("nth_partial_string_tests#2382_2", (
         G="AA",
         G=[_|Gs],
         G_=['A'|Gs],
         findall([L,C],nth0(L,G_,C),S),
         S=[[0,'A'],[1,'A']]
     )).

test("nth_partial_string_tests#2382_3", (
         G="AA",
         G=[_|Gs],
         G_=['A'|Gs],
         nth0(1,G_,C),
         C='A'
    )).


test("nth_partial_string_tests#2382_4", (
         G="XYZ",
         G=[_|Gs],
         G_=['A'|Gs],
         nth0(2,G_,C),
         C='Z'
    )).

test("nth_partial_string_tests#2382_5", (
         G="XYZ",
         G=[_|Gs],
         G_=['A'|Gs],
         nth0(2,G_,C),
         C='Z'
    )).

test("nth_partial_string_tests#2382_6", (
         G="XYZ",
         G=[_,_|T],
         nth0(0,T,C),
         C='Z'
     )).

test("nth_partial_string_tests#2382_7", (
         G="XYZ",
         G=[_,_|T],
         nth0(L,T,C),
         L=0,
         !,
         C='Z'
     )).

test("nth_partial_string_tests#2382_8", (
         G="XYZ",
         G=[_,_|T],
         L=0,
         nth0(L,T,C),
         C='Z'
     )).

test("nth_partial_string_tests#2382_9", (
         G="XYZ",
         G=[_|T],
         nth0(0,T,C),
         C='Y'
     )).

test("nth_partial_string_tests#2382_10", (
         G="XYZ",
         G=[_|T],
         nth0(1,T,C),
         C='Z'
     )).

test("nth_partial_string_tests#2382_11", (
         G="XYZ",
         T=[G|G],
         findall([L,C],nth0(L,T,C),S),
         S=[[0, "XYZ"],[1,'X'],[2,'Y'],[3,'Z']]
     )).

test("nth_partial_string_tests#2382_12", (
         G="XYZ",
         T=[G|G],
         nth0(L,T,C),
         L=3,
         !,
         C='Z'
     )).

test("nth_partial_string_tests#2382_13", (
         G="XYZ",
         T=[G|G],
         nth0(L,T,C),
         L=3,
         !,
         C='Z'
     )).

test("nth_partial_string_tests#2382_14", (
         G="XYZ",
         T=[G|G],
         L=3,
         nth0(L,T,C),
         C='Z'
     )).

test("nth_partial_string_tests#2382_15", (
         G="XYZ",
         T=[G|G],
         L=2,
         nth0(L,T,C),
         C='Y'
     )).
