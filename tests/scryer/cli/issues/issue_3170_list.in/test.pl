%% Test cases for issue #3170: (|) patterns in LIST contexts
%% When op(1105,xfy,'|') is declared, patterns like [(|)] should throw syntax_error

:- use_module(library(charsio)).
:- op(1105,xfy,'|').

%% Category 1: Simple [(|)] - should FAIL
test1 :-
    catch(
        read_term_from_chars("[(|)].", _, []),
        error(syntax_error(_), _),
        true
    ).

%% Category 2: With other elements - should FAIL
test2 :-
    catch(
        read_term_from_chars("[a,(|),b].", _, []),
        error(syntax_error(_), _),
        true
    ).

test3 :-
    catch(
        read_term_from_chars("[(|),x,y].", _, []),
        error(syntax_error(_), _),
        true
    ).

test4 :-
    catch(
        read_term_from_chars("[foo,(|)].", _, []),
        error(syntax_error(_), _),
        true
    ).

%% Category 3: With operators - should FAIL
test5 :-
    catch(
        read_term_from_chars("[!*!(|)/].", _, []),
        error(syntax_error(_), _),
        true
    ).

test6 :-
    catch(
        read_term_from_chars("[+(|)*].", _, []),
        error(syntax_error(_), _),
        true
    ).

test7 :-
    catch(
        read_term_from_chars("[-(|)].", _, []),
        error(syntax_error(_), _),
        true
    ).

%% Category 4: Multiple (|) patterns - should FAIL
test8 :-
    catch(
        read_term_from_chars("[(|),(|)].", _, []),
        error(syntax_error(_), _),
        true
    ).

test9 :-
    catch(
        read_term_from_chars("[a,(|),b,(|),c].", _, []),
        error(syntax_error(_), _),
        true
    ).

%% Category 5: Nested lists - should FAIL
test10 :-
    catch(
        read_term_from_chars("[[{(|)}]].", _, []),
        error(syntax_error(_), _),
        true
    ).

test11 :-
    catch(
        read_term_from_chars("[a,[b,(|)]].", _, []),
        error(syntax_error(_), _),
        true
    ).

test12 :-
    catch(
        read_term_from_chars("[[(|)],x].", _, []),
        error(syntax_error(_), _),
        true
    ).

test13 :-
    catch(
        read_term_from_chars("[[a,b],[(|)],[c,d]].", _, []),
        error(syntax_error(_), _),
        true
    ).

%% Category 6: VALID cases that should WORK (normal list syntax)
test14 :-
    read_term_from_chars("[a|b].", Term, []),
    Term = [a|b].

test15 :-
    read_term_from_chars("[1,2,3|Rest].", Term, []),
    Term = [1,2,3|Rest].

test16 :-
    read_term_from_chars("[x,y|[]].", Term, []),
    Term = [x,y].

test17 :-
    read_term_from_chars("[a|[b|[c|[]]]].", Term, []),
    Term = [a,b,c].

test18 :-
    read_term_from_chars("[[1,2]|[[3,4]|[]]].", Term, []),
    Term = [[1,2],[3,4]].

test19 :-
    read_term_from_chars("[foo(a,b)|tail].", Term, []),
    Term = [foo(a,b)|tail].

%% Additional edge cases - should FAIL
test20 :-
    catch(
        read_term_from_chars("[(|)|tail].", _, []),
        error(syntax_error(_), _),
        true
    ).

test21 :-
    catch(
        read_term_from_chars("[head|(|)].", _, []),
        error(syntax_error(_), _),
        true
    ).

%% Run all tests
run :-
    test1, test2, test3, test4, test5, test6, test7, test8, test9, test10,
    test11, test12, test13, test14, test15, test16, test17, test18, test19, test20,
    test21,
    halt.
