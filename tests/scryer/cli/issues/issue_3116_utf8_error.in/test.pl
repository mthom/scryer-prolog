:- use_module(library(pio)).
:- use_module(library(dcgs)).

test :-
    % Try to read invalid UTF-8 from text file containing invalid UTF-8 bytes
    catch(
        phrase_from_file(seq(_Cs), 'invalid_utf8.bin', [type(text)]),
        error(Error, _),
        (write('Error: '), write(Error), nl)
    ),
    !.
