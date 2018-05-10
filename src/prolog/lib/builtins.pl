:- op(400, yfx, /).

:- module(builtins, [(+)/2, (*)/2, (-)/2, (/)/2, (/\)/2, (\/)/2, (is)/2,
	(xor)/2, (div)/2, (//)/2, (rdiv)/2, (<<)/2, (>>)/2, (mod)/2,
	(rem)/2, (>)/2, (<)/2, (=\=)/2, (=:=)/2, (>=)/2, (=<)/2]).

% arithmetic operators.
:- op(700, xfx, is).
:- op(500, yfx, +).
:- op(500, yfx, -).
:- op(400, yfx, *).
:- op(500, yfx, /\).
:- op(500, yfx, \/).
:- op(500, yfx, xor).
:- op(400, yfx, div).
:- op(400, yfx, //).
:- op(400, yfx, rdiv).
:- op(400, yfx, <<).
:- op(400, yfx, >>).
:- op(400, yfx, mod).
:- op(400, yfx, rem).

% arithmetic comparison operators.
:- op(700, xfx, >).
:- op(700, xfx, <).
:- op(700, xfx, =\=).
:- op(700, xfx, =:=).
:- op(700, xfx, >=).
:- op(700, xfx, =<).
