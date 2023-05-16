:- module(gensym, [gensym/2,
		   reset_gensym/1]).

:- use_module(library(error)).
:- use_module(library(lists)).
:- use_module(library(iso_ext)).
:- use_module(library(si)).

gensym_key(Base, BaseKey) :-
    atom_concat('gensym_', Base, BaseKey).

append_id(Base, UniqueID, Unique) :-
    atom_chars(Base, BaseChars),
    number_chars(UniqueID, IDChars),
    append(BaseChars, IDChars, AtomChars),
    atom_chars(Unique, AtomChars).

gensym(Base, Unique) :-
    must_be(var, Unique),
    atom_si(Base),
    gensym_key(Base, BaseKey),
    (  bb_get(BaseKey, UniqueID0) -> true
    ;  UniqueID0 = 0
    ),
    UniqueID is UniqueID0 + 1,
    append_id(Base, UniqueID, Unique),
    bb_put(BaseKey, UniqueID).

reset_gensym(Base) :-
    atom_si(Base),
    bb_put(Base, 0).
