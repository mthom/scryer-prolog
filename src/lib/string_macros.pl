/** Commonly useful string macros.
 */


:- module(string_macros, [
    tel/0,
    cat/0
]).

:- use_module(library(si), [list_si/1]).
:- use_module(library(crypto), [hex_bytes/2]).
:- use_module(library(macros)).
:- use_module(library(lists), [append/3]).

%% 16 # +Hexes.
%
% Expands `Hexes` string to a list of integers (bytes).
%
% *TODO*: Add more base conversions
%
16#H ==> [B] :- list_si(H), hex_bytes(H, B).

%% tel # +Mnemonic.
%
% Expands common ASCII characters mnemonics to actual integer value.
%
% *TODO*: Add enum for every common ASCII name
%
tel#null ==> 16#"00".
tel#bell ==> 16#"07".
tel#bs   ==> 16#"08".
tel#ht   ==> 16#"09".
tel#lf   ==> 16#"0a".
tel#vt   ==> 16#"0b".
tel#ff   ==> 16#"0c".
tel#cr   ==> 16#"0d".

%% cat # (+Prefix - ?Tail).
%
% Expands to concatenation of `Prefix` and `Tail`. `Tail` can be free variable.
%
% Instead of writing this:
%
% ```
% Greeting = ['H',e,l,l,o,' '|Name].
% ```
%
% You can write:
%
% ```
% Greeting = cat#("Hello "-Name).
% ```
%
% Which gives exactly the same string.
%
cat#(Prefix-Tail) ==> inline_last#(lists:append(Prefix, Tail)).
