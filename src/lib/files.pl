/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Written June 2020 by Markus Triska (triska@metalevel.at)
   Part of Scryer Prolog.

   Predicates for reasoning about files and directories.

   In this library, directories and files are represented as
   *lists of characters*. This is an ideal representation:

   -) Lists of characters can be conveniently reasoned about with DCGs
      and built-in Prolog predicates from library(lists). This alone
      is already a very compelling argument to use them.
   -) Other Scryer libraries such as library(http/http_open) also already
      use lists of characters to represent paths.
   -) File names are mostly ephemeral, so it is good for efficiency
      that they can quickly allocated transiently on the heap, leaving the
      atom table mostly unaffected. Indexing is almost never needed
      for file names. If needed, it should be added to the engine.
   -) The previous point is also good for security, since the system
      leaves little trace of which files were even accessed.
   -) Scryer Prolog represents lists of characters extremely compactly.

   Some Prolog programmers will likely find this representation quite
   unusual, because files are represented as *atoms* in many systems.

   However, the ISO standard only demands that sources and sinks be
   *ground* terms, so lists of characters are completely admissible:

       A source/sink is specified as an implementation defined
       ground term in a call of open/4 (8.11.5). All subsequent
       references to the source/sink are made by referring to a
       stream-term (7.10.2) or alias (7.10.2.2).

   I believe that with the advent of Scryer Prolog and its efficient
   representation of strings as lists of characters, we should take
   this opportunity for improvement, and in fact extend the use of
   lists of characters also to other predicates like open/3.

   Please note that we *cannot* simply accept *both* representations,
   because that would invalidate the type errors raised by this library,
   and make future extensions for type checking impossible.

   So I ask you: Please try out this representation for a few months.
   It simplifies working with files considerably. Once we have collected
   more experience with this representations, please let us consider
   how to proceed in such a way that we can call it an improvement.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- module(files, [directory_files/2,
                  file_size/2,
                  file_exists/1,
                  directory_exists/1,
                  make_directory/1]).

:- use_module(library(error)).
:- use_module(library(lists)).

list_of_chars(Cs) :-
        must_be(list, Cs),
        maplist(must_be(character), Cs).

directory_files(Directory, Files) :-
        list_of_chars(Directory),
        can_be(list, Files),
        '$directory_files'(Directory, Files).

file_size(File, Size) :-
        list_of_chars(File),
        can_be(integer, Size),
        '$file_size'(File, Size).

file_exists(File) :-
        list_of_chars(File),
        '$file_exists'(File).

directory_exists(Directory) :-
        list_of_chars(Directory),
        '$directory_exists'(Directory).

make_directory(Directory) :-
        list_of_chars(Directory),
        '$make_directory'(Directory).
