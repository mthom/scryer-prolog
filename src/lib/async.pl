/*  library(async)

    Author:        James Tolton
    E-mail:        james.j.tolton@lotusmundi.com
    WWW:           https://www.lotusmundi.com
    Copyright (C): 2025 James J. Tolton

    Permission is hereby granted, free of charge, to any person
    obtaining a copy of this software and associated documentation
    files (the "Software"), to deal in the Software without
    restriction, including without limitation the rights to use, copy,
    modify, merge, publish, distribute, sublicense, and/or sell copies
    of the Software, and to permit persons to whom the Software is
    furnished to do so, subject to the following conditions:

    The above copyright notice and this permission notice shall be
    included in all copies or substantial portions of the Software.

    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
    EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
    MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
    HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
    WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
    OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
    DEALINGS IN THE SOFTWARE.

*/


:- module(async, [async_event_loop/1, await/1]).
:- use_module(library(queues)).
:- use_module(library(cont)).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Public API
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

%% async_event_loop(+Goals)
% Goals is a list of goals that may be asyncronous, meaning that that `await/1`
% will unify within this context and fail otherwise.

async_event_loop([]).
async_event_loop([X|Xs]) :-
        list_queue([X|Xs],Q),
        run_task_q(Q).

%% await(+Goal)
% When invoked within an `async_event_loop/1` call as an ancestor,
% the `Goal` will operate as a coroutine. Note that it is asyncronous
% but NOT concurrent or parallel without invoking an external process.

await(G) :-
        shift(zurück(G)).

/** Async Programming for Scryer Prolog

## Introduction

This library provides asyncronous semantics to Scryer Prolog users.

## Limitations

### Async, not Concurrent
Note that Scryer Prolog is currently single-threaded, and so these tools provide asyncronicity but *not* concurrency. However, a form of concurrency can be achieved by combining this library with [`library(process)`](https://www.scryer.pl/process).

### Limited options for non-blocking I/O
Right now, there are few options available for non-blocking I/O. Some gymnastics with `library(process)` are required. This will change in the near future.

## Use Cases

There are certain concepts which map well to asyncronous semantics, such as managing multiple I/O connections to external programs or anything that may need to operate in a "persistent loop" while the rest of the program continues running.

For instance, we could imagine:

```prolog

server :-
    server_options(connection_timeout_ms(Timeout)),
    wait_for_connection(Con, Timeout),
    handle_connection(Con),
    server.

```

Here, the best implementation of `handle_connection/1` is non-obvious. A signicant amount of machinery may be required, possibly involving undesirable mutational operations, in order to make the predicate non-blocking. Otherwise, `handle_connection/1` will block until the connection terminates, preventing any other connections from accessing the system.

However, with a simple adjustment:

```prolog
server_async :-
    server_options(connection_timeout_ms(Timeout)),
    wait_for_connection(Con, Timeout),
    await(handle_connection_async(Con)),
    await(server_async).


main :-
    async_event_loop([server]).

```
the server and the connections now have the ability to operate asyncronously.

You could define `handle_connection/1` as `handle_connection_async/1`:

```prolog

handle_connection_async(connection(Con)) :-
    connection_options(connection_timeout_ms(Timeout)),
    con_stream(Con,Stream),
    connection_data(Data),
    await(handle_connection_async(Data,Con,Stream,Timeout)).

handle_connection_async(partial(Data),Con,Stream,Timeout) :-
    listen_for_data(Stream,Data,NewData,Timeout),
    report_progress(Data), % output to console?
    await(handle_connection_async(NewData,Con,Stream,Timeout)).

handle_connection_async(complete(Data),Con,_Stream,_Timeout) :-
    await(handle_response_async(Data,Con)).

```

Note that there is no requirement to suffix the predicates with `_async`, but it maybe be helpful to distinguish the intent of the predicate.


### Examples Usage

```prolog


write_async(Message) :-
        write(Message),
        nl.

writem_async([Message|Messages]) :-
        await(write_async(Message)),
        await(writem_async(Messages)).
writem_async([]).


?- async_event_loop([writem_async([hello,world]), writem_async([cruel])]).
   %@ hello
   %@ cruel
   %@ world
   %@    true.
```



```prolog

:- use_module(library(async)).
:- use_module(library(random)).
:- use_module(library(clpz)).

countable_async(N,Max) :-
        if_(clpz_t(N #< Max),
            (   await(write_async(N)),
                N1#=N+1,
                await(countable_async(N1,Max))
            ),
            true
           ).

random_countable_async :-
        await(random_integer(1,10,R)),
        await(countable_async(0,R)).

   ?- async_event_loop([random_countable_async,countable_async(0,3)]).
   %@ 0
   %@ 0
   %@ 1
   %@ 1
   %@ 2
   %@ 2
   %@ 3
   %@ 4
   %@    true.

   ?- async_event_loop([writem_async([a,b,c]),countable_async(0,3)]).
   %@ a
   %@ 0
   %@ b
   %@ 1
   %@ c
   %@ 2
   %@    true.
```

## Communicating with external processes in Linux/MacOS

In this example, we create a pool of asyncronous tasks that represent some amount of work being done and then waiting for them to report completion and how long they took to complete their task. Because we do this work asyncronously, completing all tasks only takes as long as the longest task (if the number of tasks is less than the number of available processors).

In addition, the results are reported "as completed".

```prolog

:- use_module(library(async)).
:- use_module(library(process)).
:- use_module(library(charsio)).
:- use_module(library(format)).
:- use_module(library(dcgs)).
:- use_module(library(lists)).
:- use_module(library(time)).


main :-
   time(random_counting_process_tasks).

format_async(Format,Args) :-
    await(format(Format,Args)).

process_async(proc(Name, Args, Opts)) :-
        process_create(Name,Args,Opts),
        memberchk(process(Proc), Opts),
        process_async(wait(Proc,Opts)).

process_async(wait(Proc,Opts)) :-
        process_wait(Proc, Status, [timeout(0)]),
        if_(Status=exit(0),
            process_async(report(Opts)),
            process_async(reschedule(Proc,Opts))
           ) .

process_async(report(Opts)) :-
        memberchk(stdout(pipe(Stream)), Opts),
        get_n_chars(Stream,_,Chars),
        await(format_async("~s", [Chars])).

process_async(reschedule(Proc,Opts)) :-
        wait(0.01),
        await(process_async(wait(Proc,Opts))).

random_sleep_write_async(Proc) :-
        Program="N=3; rand=$(( (RANDOM % N) + 1 )); sleep $rand; echo $rand",
        Proc=process_async(proc("bash", ["-c", Program], [stdout(pipe(_Stream)), process(_P)])). 


wait(S) :-
        phrase(format_("sleep ~q", [S]), Sleep),
        process_create("bash", ["-c", Sleep], [process(P)]),
        process_wait(P, exit(0)).

random_counting_process_tasks :-
        random_counting_process_tasks(16).

random_counting_process_tasks(N) :-
        length(Tasks,N),
        maplist(random_sleep_write_async, Tasks),
        async_event_loop(Tasks).

?- main.
   %@ 1
   %@ 1
   %@ 2
   %@ 2
   %@ 2
   %@ 2
   %@ 2
   %@ 2
   %@ 2
   %@ 2
   %@ 2
   %@ 3
   %@ 3
   %@ 3
   %@ 3
   %@ 3
   %@    % CPU time: 0.185s, 230_079 inferences
   %@    true.


```

## Considerations for use with `library(cont)`

For the small minority of users working with `library(cont)`:

The mental model to keep in mind is that if an asyncronous predicate invokes `reset/3`, you are now in a *syncronous context* until `shift/1` is invoked. If you call `await/1` BEFORE calling `shift/1`, this will result in unpredictable behavior.

Remember, your `await/1` isn't worth `shift/1` if you don't `shift/1` before you `await/1`!

Example:

```prolog
:- use_module(library(async)).
:- use_module(library(cont)).

bad_target :-
        await(true),
        write(pre_shift),nl,
        shift(success).

main :-
        async_event_loop([reset(bad_target, Any, cont(Cont)), Cont]).

?- main.
%@ pre_shift
%@    false.

main1 :-
        async_event_loop([reset(bad_target, success, cont(Cont)), Cont]).

?- main1.
%@    false.


good_target :-
        shift(success),
        write(pre_await),nl,
        await(true).

main2 :-
        async_event_loop([reset(good_target, success, cont(Cont)), Cont]).

?- main2.
%@ pre_await
%@    true.
```

@author [James Tolton](https://www.lotusmundi.com)
*/

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Event Loop Helpers
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
run_task_q(q(N,A,B)) :-
        run_task_q_(N,A,B).

%% allow for arg indexing to avoid using cut w/queues
run_task_q_(s(N),A,B) :-
        taskqcall_deque(q(s(N),A,B), Nq),
        run_task_q(Nq).
run_task_q_(0,_,_).

taskqcall_deque(Q, Nq) :-
        que_item_popped(Q,T,Q0),
        handle_await(T,T1,Cont),
        resume_internal(Cont,T1,Q0,Nq).

resume_internal(none,_Meaningless,Q,Q).
resume_internal(cont(Cont),Task,Q,Nq) :-
        que_task_enque(Q,Task,Nq0),
        que_task_enque(Nq0,Cont,Nq).
        
handle_await(G,Val,Cont) :-
        reset(G, zurück(Val), Cont).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Internal Queue Implementation
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

que_item_pushed(Q, X, Nq) :-
        queue_last(X,Q,Nq).

que_item_popped(Xs,X,Nq) :-
        % API for queue_head is extremely confusing
        queue_head(X,Nq,Xs).

item_que_pushed(X,Q,Q1) :-
        que_item_pushed(Q,X,Q1).

que_task_enque(Q,T,Nq) :-
        que_item_pushed(Q,T,Nq).
