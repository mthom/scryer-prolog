% Issue 2809

:- use_module(library(freeze)).

main1 :-
  freeze(Minor,true),
  cbor_minor_value1(Minor, []).

main2 :-
  freeze(Minor,true),
  cbor_minor_value2(Minor, []).

cbor_minor_value1(24, S0) :- numbytes_number(1, S0).

cbor_minor_value2(24, S0) :- S0=S1, numbytes_number(1, S1).

numbytes_number(_, []).

test_c :- main1.
