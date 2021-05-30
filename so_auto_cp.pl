:- module(so_auto_cp, [match_list/5]).

:- use_module(library(clpfd)).
:- use_module('skip_pattern_compiler.pl').
:- use_module('event_types.pl').
:- use_module('skippable.pl').
:- use_module(library(option)).

/*
    Some runtime helpers for computing aggregate functions min and max
 */

ext_min(nothing, X, m(X)).
ext_min(m(X), Y, m(Z)) :- Z #= min(X, Y).

ext_max(nothing, X, m(X)).
ext_max(m(X), Y, m(Z)) :- Z #= max(X, Y).

fin_minmax(m(X), X).
update_avg(a(Sum0, Count0), E, a(Sum, Count))
   :- Sum #= Sum0 + E, Count #= Count0 + 1.
fin_avg(a(Sum, Count), Avg) :- Avg #= Sum // Count.

/*
     This module describes automaton recognizing patterns on lists with output.
     The automaton is defined by the following predicates:
     initial(Id, I) : initial state I for automaton Id
     final(F) : final state F
     trans(S0, A, S1) : automaton can do transition after consuming A from state
     S0 to S1
     eps(S0, S1) : automaton can do ε - transition
     skip(S, A) : automaton can skip A when in a state S.
 */

state(T), [T] --> [T].
state(T0, T1), [T1] --> [T0].
state_consume(S0, S1, T)
    --> state(
            a(S0, _, T0, C0, MaxLen), 
            a(S1, [], T, C1, MaxLen)
        ), 
        {
            C1 #= C0 + 1,
            C0 #< MaxLen,
            T0 #< T
        }.

eps_(S0, [], S1, [S1, S0])
   :- eps(S0, S1),
      dif(S0, S1). 

eps_(S0, [S0|Acc], S1, [S1, S0|Acc])
   :- eps(S0, S1),
      maplist(dif(S1), [S0|Acc]).


match_list(Id, L0, L, Out, Options)
   :- option(input(Input), Options, in),
      option(output(Output), Options, out),
      option(max_depth(MaxLen), Options, 20),
      option(max_time(MaxTime), Options, 1000),
      match_list(Id, L0, L, Out, Input, Output, MaxLen, MaxTime).

match_list(Id, L0, L, Out, Input, Output, MaxLen, MaxTime)
   :- initial(Id, Input, I),
      phrase(matcher(L0, L, Out), [a(I, [], 0, 0, MaxLen)], [a(S, _, T, _, _)]),
      T #< MaxTime,
      final(S, Output). 

list_zeroes(L0, L, _) :- var(L0), !, copy_term(L0, L).
list_zeroes([], [], []) :- !.
list_zeroes([E|L0], [E|L], [0|Out])
   :- list_zeroes(L0, L, Out).

matcher(L0, L, Out) --> {
   list_zeroes(L0, L, Out)
   }.
matcher([A|L0], [A|L], [1 | Out])
   --> {nonvar(A)},
       state_consume(S0, S1, T),
       {  
          trans(S0, A, S1),
          event_time(A, T)
       },
       matcher(L0, L, Out).
matcher([A|L0], [X, A|L], [0,1 | Out])
--> {var(A), \+ get_attr(A, skippable, _)},
    state_consume(S0, S0, Tx),
    {  
       skip(S0, X),
       trans(S0, A, S1),
       event_time(A, T),
       freeze(X, event_time(X, Tx))
    },
    state_consume(S0, S1, T),
    matcher(L0, L, Out).
matcher([A|L0], [X, A|L], [0,1 | Out])
--> {var(A), get_attr(A, skippable, _)},
    state_consume(S0, S0, Tx),
    {  
       copy_term(A, X),
       copy_term(A, Y),
       trans(S0, A, S1),
       skip(S0, X),
       freeze(A, event_time(A, T)),
       freeze(X, event_time(X, Tx))
    },
    state_consume(S0, S1, T),
    matcher([Y|L0], L, Out).
matcher(L0, L, Out)
   --> state(
         a(S0, Acc0, T, C, MaxLen), 
         a(S1, Acc1, T, C, MaxLen)
       ),
       {
          eps_(S0, Acc0, S1, Acc1)
       },
       matcher(L0, L, Out).
matcher([A|L0], [A|L], [0|Out])
   --> {nonvar(A) ; get_attr(A, skippable, _)},
       state_consume(S, S, T),
       {
          freeze(A, event_time(A, T)),
          skip(S, A)
       },
       matcher(L0, L,  Out).
