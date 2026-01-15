:- use_module(library(format)).
:- use_module(library(pio)).

% Define a DCG that produces the phrase
hello_phrase --> 
    "Hello, Prolog world!\n".

%write something to the user output stream.
hello_world :-
        phrase_to_stream(hello_phrase, user_output).