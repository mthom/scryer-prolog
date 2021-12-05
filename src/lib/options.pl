/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   library(options) simplifies option processing.

   The most important, and currently only, predicate is option/3,
   used as:

       option(Option, Options, Default)

   Options must be a list of options. An option is a non-variable term
   of the form name(Value). If Options does not contain an option of
   the specified name, then Default is used as Value.

   Examples:

      ?- option(tls(TLS), [], false).
      %@    TLS = false.

      ?- option(tls(TLS), [tls(true)], false).
      %@    TLS = true.

- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- module(options, [option/3]).

:- use_module(library(error)).
:- use_module(library(lists)).

option(Option, Options, Default) :-
        (   var(Option) ->
            instantiation_error(option(Option))
        ;   true
        ),
        must_be(list, Options),
        (   member(Var, Options), var(Var) ->
            instantiation_error(option(Var))
        ;   true
        ),
        (   member(Option, Options) -> true
        ;   Option =.. [_,Default]
        ).
