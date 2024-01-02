 /* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Predicates for reasoning about the operating system (OS) environment.
   Written July 2020 by Markus Triska (triska@metalevel.at).

   Lists of characters are used throughout to represent keys and values.

   Example:

       ?- getenv("LANG", Ls).
          Ls = "en_US.UTF-8".

   Public domain code.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

/** Predicates for reasoning about the operating system (OS) environment.

This includes predicates about environment variables, calls to shell and
finding out the PID of the running system.
*/

:- module(os, [getenv/2,
               setenv/2,
               unsetenv/1,
               shell/1,
               shell/2,
               pid/1,
	       raw_argv/1,
	       argv/1]).

:- use_module(library(error)).
:- use_module(library(charsio)).
:- use_module(library(lists)).
:- use_module(library(si)).

%% getenv(+Key, -Value).
%
% True iff Value contains the value of the environment variable Key.
% Example:
%
% ```
% ?- getenv("LANG", Ls).
%    Ls = "en_US.UTF-8".
% ```
getenv(Key, Value) :-
        must_be_env_var(Key),
        '$getenv'(Key, Value).

%% setenv(+Key, +Value).
%
% Sets the environment variable Key to Value
setenv(Key, Value) :-
        must_be_env_var(Key),
        must_be_chars(Value),
        '$setenv'(Key, Value).

%% unsetenv(+Key).
%
% Unsets the environment variable Key
unsetenv(Key) :-
        must_be_env_var(Key),
        '$unsetenv'(Key).

%% shell(+Command)
%
% Equivalent to `shell(Command, 0)`.
shell(Command) :- shell(Command, 0).

%% shell(+Command, -Status).
%
% True iff executes Command in a shell of the operating system and the exit code is Status.
% Keep in mind the shell syntax is dependant on the operating system, so it should be
% used very carefully.
%
% Example (using Linux and fish shell):
%
% ```
% ?- shell("echo $SHELL", Status).
% /bin/fish
%    Status = 0.
% ```
shell(Command, Status) :-
    must_be_chars(Command),
    can_be(integer, Status),
    '$shell'(Command, Status).

%% pid(-PID).
%
% True iff PID is the process identification number of current Scryer Prolog instance.
pid(PID) :-
        can_be(integer, PID),
        '$pid'(PID).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   For now, we only support a restricted subset of variable names.

   The reason is that Rust may panic if a key is empty, contains an
   ASCII equals sign '=' or the NUL character '\0', or when the value
   contains the NUL character.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

must_be_env_var(Cs) :-
        must_be_chars(Cs),
        Cs = [_|_],
        (   maplist(permitted, Cs) -> true
        ;   domain_error(env_var, Cs, os)
        ).

permitted(C) :- char_type(C, alnum).
permitted(C) :- char_type(C, ascii_punctuation).
permitted('_').

must_be_chars(Cs) :-
        must_be(list, Cs),
        maplist(must_be(character), Cs).

%% raw_argv(-Argv)
%
% True iff Argv is the list of arguments that this program was started with (usually passed via command line).
% In contrast to `argv/1`, this version includes every argument, without any postprocessing, just as the operating
% system reports it to the system. This includes-flags of Scryer itself, which are not needed in general.
raw_argv(Argv) :-
    can_be(list, Argv),
    '$argv'(Argv).

%% argv(-Argv)
%
% True if Argv is the list of arguments that this program was started with (usually passed via command line).
% In this version, only arguments specific to the program are passed. To differentiate between the system
% arguments and the program arguments, we use `--` as a separator.
%
% Example:
% ```
% % Call with scryer-prolog -f -- -t hello
% ?- argv(X).
%     X = ["-t", "hello"].
% ```
argv(Argv) :-
    can_be(list, Argv),
    '$argv'(Argv0),
    ( member("--", Argv0) ->
        append(Argv1, ["--"|Argv], Argv0),
        \+ member("--", Argv1),
        !
    ;
        Argv = []
    ).
