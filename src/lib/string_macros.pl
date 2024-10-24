:- module(string_macros, [
    macro/3
]).

:- use_module(library(si), [list_si/1]).
:- use_module(library(crypto), [hex_bytes/2]).
:- use_module(library(macros)).

% Base conversion
16#H ==> [B] :- list_si(H), hex_bytes(H, B).

% String enums
tel#null ==> 16#"00".
tel#bell ==> 16#"07".
tel#bs   ==> 16#"08".
tel#ht   ==> 16#"09".
tel#lf   ==> 16#"0a".
tel#vt   ==> 16#"0b".
tel#ff   ==> 16#"0c".
tel#cr   ==> 16#"0d".
