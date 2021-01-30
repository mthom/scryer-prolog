% Unsure how to handle the printing of exceptions from term & goal expansion.

'$print_message_and_fail'(Error, Culprit) :-
%    writeq(error(Error, Culprit)),
%    nl,
    '$fail'.

term_expansion(Term, ExpandedTerm) :-
    (  catch(user:'$term_expansion'(Term, ExpandedTerm0),
             E,
             user:'$print_message_and_fail'(E, user:term_expansion)) ->
       (  var(ExpandedTerm0) ->
          error:instantiation_error(term_expansion/2)
       ;  ExpandedTerm0 = [_|_] ->
          term_expansion_list(ExpandedTerm0, ExpandedTerm, [])
       ;  term_expansion(ExpandedTerm0, ExpandedTerm)
       )
    ;  Term = ExpandedTerm
    ).


term_expansion_list([], ExpandedTerms, ExpandedTerms).
term_expansion_list([Term|Terms], ExpandedTermsHead, ExpandedTermsTail) :-
    term_expansion(Term, ExpandedTerm0),
    (  var(ExpandedTerm0) ->
       error:instantiation_error(term_expansion/2)
    ;  ExpandedTerm0 = [_|_] ->
       term_expansion_list(ExpandedTerm0, ExpandedTermsHead, ExpandedTerms0Tail),
       term_expansion_list(Terms, ExpandedTerms0Tail, ExpandedTermsTail)
    ;  ExpandedTermsHead = [ExpandedTerm0 | ExpandedTerms0Tail],
       term_expansion_list(Terms, ExpandedTerms0Tail, ExpandedTermsTail)
    ).


goal_expansion(Goal, Module, ExpandedGoal) :-
    (  catch(Module:goal_expansion(Goal, ExpandedGoal0),
             E,
             user:'$print_message_and_fail'(E, Module:goal_expansion)) ->
       (  var(ExpandedGoal0) ->
          error:instantiation_error(goal_expansion/2)
       ;  goal_expansion(ExpandedGoal0, Module, ExpandedGoal)
       )
    ;  Goal = ExpandedGoal
    ).
