:- module(queues, [queue/1, queue/2, queue_head/3, queue_head_list/3,
		   queue_last/3, queue_last_list/3, list_queue/2,
		   queue_length/2]).

/* true when Queue is a queue with no elements. */
queue(q(0,B,B)).

/* true when Queue is a queue with one element. */
queue(X, q(s(0), [X|B], B)).

/* true when Queue0 and Queue1 have the same elements except that
 * Queue0 has in addition X at the front.  Use it for enqueuing and
 * dequeuing both.
*/
queue_head(X, q(N, F, B), q(s(N), [X|F], B)).

/* true when append(List, Queue1, Queue0) would be true if only Queue1
 * and Queue0 were lists instead of queues.
*/
queue_head_list([], Queue, Queue).
queue_head_list([X|Xs], Queue, Queue0) :-
    queue_head(X, Queue1, Queue0),
    queue_head_list(Xs, Queue, Queue1).

/* true when Queue0 and Queue1 have the same elements except that
 * Queue0 has in addition to X at the end.
*/
queue_last(X, q(N, F, [X|B]), q(s(N), F, B)).

/* true when append(Queue1, List, Queue0) would be true if only Queue1
 * and Queue0 were lists instead of queues.
*/
queue_last_list([], Queue, Queue).
queue_last_list([X|Xs], Queue1, Queue) :-
    queue_last(X, Queue1, Queue2),
    queue_last_list(Xs, Queue2, Queue).

/* true when List is a list and Queue is a queue and they represent
 * the same sequence.
*/
list_queue(List, q(Count, Front, Back)) :-
    list_queue(List, Count, Front, Back).

list_queue([], 0, B, B).
list_queue([X|Xs], s(N), [X|F], B) :-
    list_queue(Xs, N, F, B).

/* is true when Length is (a binary length representing) the number of
 * elements in (the queue represented by) Queue. This version cannot
 * be used to generate a Queue, only to determine the Length.
*/
queue_length(q(Count, F, B), Length) :-
    queue_length(Count, F, B, 0, Length).

queue_length(0, B, B, Length, Length).
queue_length(s(N), [_|Front], Back, L0, Length) :-
    L1 is L0 + 1,
    queue_length(N, Front, Back, L1, Length).
