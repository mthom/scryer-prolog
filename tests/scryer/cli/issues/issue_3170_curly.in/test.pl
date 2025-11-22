%% Comprehensive test cases for issue #3170
%% Testing (|) patterns inside curly braces with op(1105,xfy,'|')
%% All patterns should throw syntax_error, not produce artifacts
%%
%% ISO/IEC 13211-1:1995 References:
%% - §6.3.3.1: Arguments have priority ≤999 (to avoid conflict with comma at 1000)
%% - §6.3.4: Operator Notation - operators require operands based on their specifier
%% - §6.3.4.2: Operators as Functors - '|' when declared as operator (priority 1105)
%% - §6.3.6: Curly Bracketed Term - {term} == '{}'(term)
%%           Examples: {a} == '{}'(a), {a,b} == '{}'(','(a,b))
%%           Commas inside {} are comma OPERATOR (priority 1000), not list separators
%%
%% When op(1105,xfy,'|') is declared:
%% - '|' becomes an operator requiring two operands (xfy = infix right-associative)
%% - (|) means "operator without operands" which violates §6.3.4 requirements
%% - Inside {}, the argument must be a valid term (§6.3.6), but (|) is not
%% - Therefore {(|)} and variants must produce syntax_error

:- use_module(library(charsio)).
:- op(1105, xfy, '|').

%% Category 1: Different trailing operators with ! prefix

test1 :-
    % {!*!(|)/} - original issue pattern
    catch(read_from_chars("{!*!(|)/}", _),
          error(syntax_error(_), _),
          true).

test2 :-
    % {!*!(|)*} - trailing multiplication
    catch(read_from_chars("{!*!(|)*}", _),
          error(syntax_error(_), _),
          true).

test3 :-
    % {!*!(|)+} - trailing plus
    catch(read_from_chars("{!*!(|)+}", _),
          error(syntax_error(_), _),
          true).

test4 :-
    % {!*!(|)-} - trailing minus
    catch(read_from_chars("{!*!(|)-}", _),
          error(syntax_error(_), _),
          true).

test5 :-
    % {!*!(|)//} - trailing integer division
    catch(read_from_chars("{!*!(|)//}", _),
          error(syntax_error(_), _),
          true).

test6 :-
    % {!*!(|)**} - trailing power
    catch(read_from_chars("{!*!(|)**}", _),
          error(syntax_error(_), _),
          true).

%% Category 2: Different prefix operators

test7 :-
    % {!+(|)/} - ! and + prefix
    catch(read_from_chars("{!+(|)/}", _),
          error(syntax_error(_), _),
          true).

test8 :-
    % {*!(|)/} - * prefix with ! infix
    catch(read_from_chars("{*!(|)/}", _),
          error(syntax_error(_), _),
          true).

test9 :-
    % {++(|)/} - double + prefix
    catch(read_from_chars("{++(|)/}", _),
          error(syntax_error(_), _),
          true).

test10 :-
    % {--(|)/} - double - prefix
    catch(read_from_chars("{--(|)/}", _),
          error(syntax_error(_), _),
          true).

test11 :-
    % {!!(|)/} - double ! prefix
    catch(read_from_chars("{!!(|)/}", _),
          error(syntax_error(_), _),
          true).

test12 :-
    % {+-!(|)/} - mixed prefix operators
    catch(read_from_chars("{+-!(|)/}", _),
          error(syntax_error(_), _),
          true).

%% Category 3: Multiple trailing operators

test13 :-
    % {!*!(|)///} - triple slash
    catch(read_from_chars("{!*!(|)///}", _),
          error(syntax_error(_), _),
          true).

test14 :-
    % {!*!(|)****} - quadruple star
    catch(read_from_chars("{!*!(|)****}", _),
          error(syntax_error(_), _),
          true).

test15 :-
    % {!*!(|)//*/} - mixed trailing operators
    catch(read_from_chars("{!*!(|)//*/}", _),
          error(syntax_error(_), _),
          true).

test16 :-
    % {!*!(|)++-} - multiple plus and minus
    catch(read_from_chars("{!*!(|)++-}", _),
          error(syntax_error(_), _),
          true).

%% Category 4: Just (|) with minimal operators

test17 :-
    % {(|)} - bare (|) in curly braces
    catch(read_from_chars("{(|)}", _),
          error(syntax_error(_), _),
          true).

test18 :-
    % {!(|)} - single prefix operator
    catch(read_from_chars("{!(|)}", _),
          error(syntax_error(_), _),
          true).

test19 :-
    % {(|)/} - single trailing operator
    catch(read_from_chars("{(|)/}", _),
          error(syntax_error(_), _),
          true).

test20 :-
    % {+(|)-} - single prefix and trailing
    catch(read_from_chars("{+(|)-}", _),
          error(syntax_error(_), _),
          true).

%% Category 5: Nested expressions with atoms/variables

test21 :-
    % {a*(|)+b} - atoms around (|)
    catch(read_from_chars("{a*(|)+b}", _),
          error(syntax_error(_), _),
          true).

test22 :-
    % {foo+(|)-bar} - named atoms
    catch(read_from_chars("{foo+(|)-bar}", _),
          error(syntax_error(_), _),
          true).

test23 :-
    % {X*(|)/Y} - variables around (|)
    catch(read_from_chars("{X*(|)/Y}", _),
          error(syntax_error(_), _),
          true).

test24 :-
    % {1+(|)*2} - numbers around (|)
    catch(read_from_chars("{1+(|)*2}", _),
          error(syntax_error(_), _),
          true).

test25 :-
    % {abc-(|)//xyz} - longer expressions
    catch(read_from_chars("{abc-(|)//xyz}", _),
          error(syntax_error(_), _),
          true).

%% Category 6: More complex operator combinations

test26 :-
    % {!*!*!(|)/} - extended prefix chain
    catch(read_from_chars("{!*!*!(|)/}", _),
          error(syntax_error(_), _),
          true).

test27 :-
    % {(|)/*/**} - complex trailing chain
    catch(read_from_chars("{(|)/*/**}", _),
          error(syntax_error(_), _),
          true).

test28 :-
    % {-+*!(|)+*-} - symmetric operator pattern
    catch(read_from_chars("{-+*!(|)+*-}", _),
          error(syntax_error(_), _),
          true).

%% Category 7: Edge cases with parentheses variations

test29 :-
    % {((|))/} - double parentheses
    catch(read_from_chars("{((|))/}", _),
          error(syntax_error(_), _),
          true).

test30 :-
    % {!(|(|))/} - nested | operator
    catch(read_from_chars("{!(|(|))}", _),
          error(syntax_error(_), _),
          true).

%% Category 8: Whitespace variations

test31 :-
    % { ! * ! ( | ) / } - with spaces
    catch(read_from_chars("{ ! * ! ( | ) / }", _),
          error(syntax_error(_), _),
          true).

test32 :-
    % {  (|)  /  } - extra whitespace
    catch(read_from_chars("{  (|)  /  }", _),
          error(syntax_error(_), _),
          true).

%% Run all tests
run :-
    test1, test2, test3, test4, test5, test6, test7, test8, test9, test10,
    test11, test12, test13, test14, test15, test16, test17, test18, test19, test20,
    test21, test22, test23, test24, test25, test26, test27, test28, test29, test30,
    test31, test32,
    halt.
