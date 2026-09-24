:- use_module(library(charsio)).

test2 :-
    % Test direct get_n_chars with invalid UTF-8
    open('invalid_utf8.bin', read, Stream, [type(text)]),
    catch(
        get_n_chars(Stream, 10, _Cs),
        error(Error, _),
        (write('Error: '), write(Error), nl)
    ),
    close(Stream).
