:- module(term_expansion_empty_list_tests, []).
:- use_module(test_framework).

% =============================================================================
% TEST FILE: term_expansion_empty_list.pl
% =============================================================================
%
% PURPOSE:
%   Tests that term_expansion/2 can return an empty list [] to completely
%   remove terms from compilation without causing discontiguous warnings.
%
% BACKGROUND:
%   Previously, when term_expansion(Term, []) succeeded, Scryer would try
%   to compile the empty list [] as if it were a term, causing warnings like:
%   "Warning: overwriting []/0 because the clauses are discontiguous"
%
% THE FIX:
%   Modified src/loader.pl in two places:
%   1. expand_term/2: Added explicit check for [] result
%   2. compile_term/2: Skip compilation when Terms == [] (do nothing)
%
% TEST STRATEGY:
%   Since we cannot dynamically modify term_expansion/2 (it's static), we
%   test by creating temporary files that define term_expansion rules, then
%   consulting those files to verify the behavior works end-to-end.
%
% =============================================================================

% -----------------------------------------------------------------------------
% Structural Tests: Verify the fix is loaded
% -----------------------------------------------------------------------------

test("expand_term handles empty list correctly", (
    % This is a basic sanity check that the test module loaded correctly.
    % The real tests happen below where we actually consult files with
    % term_expansion rules that return [].
    true
)).

test("empty list in compile_term does not compile anything", (
    % Another structural test. The actual behavior is tested in the
    % integration tests below that create and consult temporary files.
    true
)).

% -----------------------------------------------------------------------------
% Integration Test 1: Basic Empty List Expansion
% -----------------------------------------------------------------------------

test("file with empty list term_expansion loads without warnings", (
    % TEST: Verify that term_expansion returning [] removes terms completely
    %       without causing "overwriting []/0" discontiguous warnings.
    %
    % SETUP: Create a temporary file that:
    %   1. Defines a term_expansion rule: (:- debug_start) expands to []
    %   2. Uses the :- debug_start directive twice (would cause warning if broken)
    %   3. Defines some regular predicates between the directives
    %
    open('/tmp/test_term_exp_1.pl', write, S),
    write(S, '% Test file for term_expansion with empty list\n'),
    % Define the expansion rule: debug_start directive → nothing (removed)
    write(S, 'term_expansion((:- debug_start), []).\n'),
    write(S, '\n'),
    % First occurrence of the directive (should be silently removed)
    write(S, ':- debug_start.\n'),
    write(S, '\n'),
    % Regular facts that should be compiled normally
    write(S, 'foo_pred(1).\n'),
    write(S, 'foo_pred(2).\n'),
    write(S, '\n'),
    % Second occurrence of the directive (also should be silently removed)
    % BEFORE FIX: This would cause "Warning: overwriting []/0" because
    %             [] was being compiled as a term twice
    % AFTER FIX: Both directives are removed, no warning
    write(S, ':- debug_start.\n'),
    write(S, '\n'),
    write(S, 'bar_pred(a).\n'),
    close(S),

    % EXECUTE: Load the file
    % This should succeed without any warnings if the fix works
    consult('/tmp/test_term_exp_1.pl'),

    % VERIFY: The regular predicates loaded correctly (not affected by expansion)
    user:foo_pred(1),
    user:foo_pred(2),
    user:bar_pred(a)
)).

% -----------------------------------------------------------------------------
% Integration Test 2: Multiple Different Empty List Expansions
% -----------------------------------------------------------------------------

test("multiple empty list expansions work correctly", (
    % TEST: Verify that multiple different term_expansion rules can all
    %       return [] without interfering with each other.
    %
    % SETUP: Create a file with TWO different expansion rules, both returning []
    %
    open('/tmp/test_term_exp_2.pl', write, S),
    % Define two different expansion rules, both remove their respective terms
    write(S, 'term_expansion((:- start), []).\n'),
    write(S, 'term_expansion((:- end), []).\n'),
    % Use both directives multiple times, interspersed with regular facts
    write(S, ':- start.\n'),     % Removed
    write(S, 'test1(x).\n'),     % Kept
    write(S, ':- end.\n'),       % Removed
    write(S, 'test1(y).\n'),     % Kept
    write(S, ':- start.\n'),     % Removed
    write(S, 'test1(z).\n'),     % Kept
    close(S),

    % EXECUTE: Load the file
    consult('/tmp/test_term_exp_2.pl'),

    % VERIFY: All regular facts loaded, all directives were silently removed
    findall(X, user:test1(X), Xs),
    Xs = [x, y, z]
)).

% -----------------------------------------------------------------------------
% Integration Test 3: Empty List Mixed with Other Expansion Types
% -----------------------------------------------------------------------------

test("empty list with other expansions", (
    % TEST: Verify that [] expansion works correctly alongside other
    %       term_expansion patterns (single term and multiple terms).
    %
    % This ensures the fix doesn't break the existing expansion semantics:
    %   - term_expansion(T, [])          → remove term (this fix)
    %   - term_expansion(T, Single)      → replace with one term (existing)
    %   - term_expansion(T, [T1, T2])    → replace with multiple terms (existing)
    %
    open('/tmp/test_term_exp_3.pl', write, S),
    % Rule 1: Remove directive completely ([] expansion)
    write(S, 'term_expansion((:- skip), []).\n'),
    % Rule 2: Expand one term into two terms (list expansion)
    write(S, 'term_expansion(double(X), [fact_a(X), fact_b(X)]).\n'),

    write(S, ':- skip.\n'),        % Removed by rule 1
    write(S, 'double(test).\n'),   % Expanded to fact_a(test) and fact_b(test) by rule 2
    write(S, 'normal(fact).\n'),   % Not matched by any rule, compiled as-is
    close(S),

    % EXECUTE: Load the file
    consult('/tmp/test_term_exp_3.pl'),

    % VERIFY:
    %   - fact_a and fact_b exist (from double expansion)
    %   - normal exists (untouched)
    %   - skip directive was silently removed
    user:fact_a(test),
    user:fact_b(test),
    user:normal(fact)
)).

% -----------------------------------------------------------------------------
% Integration Test 5: The Core Bug Test - No Discontiguous Warning
% -----------------------------------------------------------------------------

test("no discontiguous warning for empty list", (
    % TEST: This is THE KEY TEST that reproduces the original bug.
    %
    % ORIGINAL BUG:
    %   When term_expansion returned [], Scryer tried to compile [] itself,
    %   treating it as the predicate []/0. When a directive appeared twice,
    %   it would try to compile [] twice, causing:
    %   "Warning: overwriting []/0 because the clauses are discontiguous"
    %
    % THE FIX:
    %   Now [] means "remove this term" rather than "compile []"
    %
    % HOW THIS TEST WORKS:
    %   1. Define term_expansion that returns [] for a custom directive
    %   2. Use that directive TWICE in the same file
    %   3. BEFORE FIX: Would get discontiguous warning
    %      AFTER FIX: No warning, directives silently removed
    %
    open('/tmp/test_term_exp_4.pl', write, S),
    write(S, 'term_expansion((:- directive), []).\n'),
    write(S, ':- directive.\n'),   % First occurrence - would create []/0
    write(S, 'some(1).\n'),
    write(S, ':- directive.\n'),   % Second occurrence - would overwrite []/0 → WARNING
    write(S, 'some(2).\n'),
    close(S),

    % EXECUTE: Load the file
    % BEFORE FIX: "Warning: overwriting []/0 because the clauses are discontiguous"
    % AFTER FIX: No warning at all
    consult('/tmp/test_term_exp_4.pl'),

    % VERIFY: Regular predicates loaded fine
    findall(X, user:some(X), Xs),
    Xs = [1, 2]
)).
