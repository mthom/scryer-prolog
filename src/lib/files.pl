/** Predicates for reasoning about files and directories.

In this library, directories and files are represented as
_lists of characters_. This is an ideal representation:

* Lists of characters can be conveniently reasoned about with DCGs
   and built-in Prolog predicates from `library(lists)`. This alone
   is already a very compelling argument to use them.
* Other Scryer libraries such as `library(http/http_open)` also already
   use lists of characters to represent paths.
* File names are mostly ephemeral, so it is good for efficiency
   that they can quickly allocated transiently on the heap, leaving the
   atom table mostly unaffected. Indexing is almost never needed
   for file names. If needed, it should be added to the engine.
* The previous point is also good for security, since the system
   leaves little trace of which files were even accessed.
* Scryer Prolog represents lists of characters extremely compactly.
*/

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Written 2020, 2022 by Markus Triska (triska@metalevel.at)
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
                  delete_file/1,
		          rename_file/2,
		          file_copy/2,
		          delete_directory/1,
                  make_directory/1,
                  make_directory_path/1,
                  working_directory/2,
                  path_canonical/2,
                  path_segments/2,
                  file_modification_time/2,
                  file_creation_time/2,
                  file_access_time/2]).

:- use_module(library(error)).
:- use_module(library(lists)).
:- use_module(library(charsio)).
:- use_module(library(dcgs)).

%% directory_files(+Directory, -Files).
%
% Returns the list of files *and* directories available at a specific
% directory in the current system.

directory_files(Directory, Files) :-
        must_be(chars, Directory),
        can_be(list, Files),
        '$directory_files'(Directory, Files).

%% file_size(+File, -Size).
%
% Returns the size (in bytes) of a file. The file must exist.

file_size(File, Size) :-
        file_must_exist(File, file_size/2),
        can_be(integer, Size),
        '$file_size'(File, Size).

%% file_exists(+File).
%
% Succeeds if File is a file that exists in the current system.
file_exists(File) :-
        must_be(chars, File),
        '$file_exists'(File).

%% directory_exists(+Directory).
%
% Succeeds if Directory is a directory that exists in the current system.
directory_exists(Directory) :-
        must_be(chars, Directory),
        '$directory_exists'(Directory).

%% make_directory(+Directory).
%
% Succeeds if it creates a new directory named Directory in the current system.
% If you want to create a nested directory, use `make_directory_path/1`.
make_directory(Directory) :-
        must_be(chars, Directory),
        '$make_directory'(Directory).

%% make_directory_path(+Directory).
%
% Similar to `make_directory/1` but recursively creates directories if they're missing.
% Equivalent to mkdir -p in Unix.
make_directory_path(Directory) :-
        must_be(chars, Directory),
        '$make_directory_path'(Directory).

%% delete_file(+File).
%
% Succeeds if deletes File from the current system.
delete_file(File) :-
        file_must_exist(File, delete_file/1),
        '$delete_file'(File).

%% rename_file(+File, +Renamed).
%
% Succeeds if File is renamed to Renamed
rename_file(File, Renamed) :-
        file_must_exist(File, rename_file/2),
        must_be(chars, Renamed),
        '$rename_file'(File, Renamed).

%% file_copy(+File, +Copied).
%
% Succeeds if File is copied to Copied
file_copy(File, Copied) :-
	file_must_exist(File, file_copy/2),
	must_be(chars, Copied),
	'$file_copy'(File, Copied).

%% delete_directory(+Directory).
%
% Succeeds if Directory is deleted from the current system.
% Directory must be empty.
delete_directory(Directory) :-
        directory_must_exist(Directory, delete_directory/1),
        must_be(chars, Directory),
        '$delete_directory'(Directory).

file_must_exist(File, Context) :-
        (   file_exists(File) -> true
        ;   throw(error(existence_error(file, File), Context))
        ).

directory_must_exist(Directory, Context) :-
        (   directory_exists(Directory) -> true
        ;   throw(error(existence_error(directory, Directory), Context))
        ).

%% workind_directory(Dir0, Dir).
%
% Dir0 is the current working directory, and the working directory
% is changed to Dir.
% 
% Use `working_directory/2` to determine the current working directory,
% and leave it as is.

working_directory(Dir0, Dir) :-
        can_be(list, Dir0),
        can_be(list, Dir),
        '$working_directory'(Dir0, Dir).

%% path_canonical(Ps, Cs).
%
% True iff Cs is the canonical, absolute path of Ps.
%
% All intermediate components are normalized, and all symbolic links
% are resolved.
%
% The predicate fails in the following situations, though not
% necessarily *only* in these cases:
%
% 1. Ps is a path that does not exist.
% 2. A non-final component in Ps is not a directory.

path_canonical(Ps, Cs) :-
        must_be(chars, Ps),
        can_be(list, Cs),
        '$path_canonical'(Ps, Cs).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   T is, respectively, the modification, access or creation time of File.
   T is a time stamp, suitable for use in format_time//2 in library(time).

   For two time stamps A and B, if A precedes B, then A @< B holds.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

%% file_modification_time(+File, -T).
%
% For a file File that must exist, it returns a time stamp  T with the modification time
%
% T is a time stamp compatible with `library(time)`. 
file_modification_time(File, T) :-
        file_time_(File, modification, T).

%% file_access_time(+File, -T).
%
% For a file File that must exist, it returns a time stamp  T with the access time
%
% T is a time stamp compatible with `library(time)`.
file_access_time(File, T) :-
        file_time_(File, access, T).

%% file_creation_time(+File, -T).
%
% For a file File that must exist, it returns a time stamp  T with the creation time
%
% T is a time stamp compatible with `library(time)`.
file_creation_time(File, T) :-
        file_time_(File, creation, T).

file_time_(File, Which, T) :-
        file_must_exist(File, file_time_/3),
        '$file_time'(File, Which, T0),
        read_from_chars(T0, T).


%% path_segments(Ps, Segments).
%
% True iff Segments are the segments of Ps.
%
% Segments is the list of components of the path Ps that are
% separated by the platform-specific directory separator. Each
% segment is a list of characters.
%
% At least one of the arguments must be instantiated.
%
% Examples:
%
% ```
% ?- path_segments("/hello/there", Segments).
%    Segments = [[],"hello","there"].
% ?- path_segments(Path, ["hello","there"]).
%    Path = "hello/there".
% ```
% 
% To obtain the platform-specific directory separator, you can use:
%
% ```
% ?- path_segments(Separator, ["",""]).
%    Separator = "/".
% ```

path_segments(Path, Segments) :-
        '$directory_separator'(Sep),
        (   var(Path) ->
            must_be(list, Segments),
            maplist(must_be(chars), Segments),
            phrase(append_with_separator(Segments, Sep), Path)
        ;   must_be(chars, Path),
            path_to_segments(Path, Sep, Segments)
        ).

append_with_separator([], _) --> [].
append_with_separator([Segment|Segments], Sep) -->
        append_with_separator_(Segments, Segment, Sep).

append_with_separator_([], Segment, _) --> seq(Segment).
append_with_separator_([Segment|Segments], Prev, Sep) -->
        seq(Prev), [Sep],
        append_with_separator_(Segments, Segment, Sep).

path_to_segments(Path, Sep, Segments) :-
        (   append(Front, [Sep|Ps], Path) ->
            Segments = [Front|Rest],
            path_to_segments(Ps, Sep, Rest)
        ;   Segments = [Path]
        ).
