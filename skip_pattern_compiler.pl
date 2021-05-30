:- module(skip_pattern_compiler, [
     assert_regular/2
]).

:- use_module(library(clpfd)).
:- use_module(library(ordsets)).
:- use_module(library(varnumbers)).
:- use_module(library(pairs)).
:- use_module('skip_pattern_syntax.pl').
:- use_module('compiler_state.pl').
:- use_module('compiler_helpers.pl').
:- use_module('skippable.pl').


/*
    Automatons are represented (during compilation) by dicts of the form
    auto{
         transitions: [trans(V, Type, S0, S1):-G, ...],
         epses: [eps(S0, S1), ...],
         skips: [skip(S, V1, event_specs)],
         initial: S,
         final: [S, ...]
    }
    where event_specs is a list of pairs type-condition.
    An event E is skippable in state S0 iff its type either is not on the list skips or it is 
    and then the condition is satisfied. The variable V1 is used
    to refer to the event under consideration in all the conditions.
*/

compile_query_pure(Id, Pattern, M0, Vs, Automaton)
    :- %numbervars(Pattern, 0, M0),
       init_state(M0, Id, Vs, InitialState),
       phrase(comp_aut(Pattern, Automaton), InitialState, [_]).

comp_aut(empty, auto{
        transitions: [],
        epses: [],
        skips: [],
        initial: S,
        final: [S]
    })
    --> current_vars(Vs),
        fresh_state(S, Vs).

comp_aut(
   event(Type, V), auto{
        transitions: [(trans(V, Type, S0, S1) :- true)],
        epses: [],
        initial: S0,
        skips: [skip(S0, V1, [])],
        final: [S1]
   }) 
   --> fresh_var(V1),
       replace_vars(Vs0, Vs),
       {ord_add_element(Vs0, V, Vs)},
       fresh_states([S0, S1], [Vs0, Vs]).

comp_aut(P1 then P2, auto{
   transitions: Ts,
   epses: Es,
   initial: I,
   skips: Skips,
   final: F
})
--> 
    comp_aut(P1, Auto1),
    comp_aut(P2, Auto2),
    {
      I = Auto1.initial,
      F = Auto2.final,
      append(Auto1.transitions, Auto2.transitions, Ts),
      append(Auto1.epses, Auto2.epses, Es0),
      append(Auto1.skips, Auto2.skips, Skips),
      sources_target_acc_epses(Auto1.final, Auto2.initial, Es0, Es)
    }.

comp_aut(P1 or P2, auto{
   transitions: Ts,
   epses: [(eps(S0, I1) :- true), (eps(S0, I2) :- true)|Es],
   skips: Skips,
   initial: S0,
   final: Fs
})
   --> current_vars(Vs0),
       comp_aut(P1, Auto1),
       replace_vars(Vs1, Vs0),
       comp_aut(P2, Auto2),
       replace_vars(Vs2, Vs),
       {
          I1 = Auto1.initial,
          I2 = Auto2.initial,
          ord_intersection(Vs1, Vs2, Vs),
          append(Auto1.transitions, Auto2.transitions, Ts),
          append(Auto1.epses, Auto2.epses, Es),
          append(Auto1.skips, Auto2.skips, Skips),
          append(Auto1.final, Auto2.final, Fs)
       },
       fresh_state(S0, Vs0).

comp_aut(P1 and P2, auto{
   transitions: Trans,
   epses: [(eps(NewInit, I) :- true), (eps(F, NewFinal) :- true)|Es],
   skips: Skips,
   initial: NewInit,
   final: [NewFinal]
})
   --> current_vars(Vs0),
       comp_aut(P1, Auto10),
       replace_vars(Vs1, Vs0),
       comp_aut(P2, Auto20),
       replace_vars(Vs2, Vs),
       {
          ord_union(Vs1, Vs2, Vs)
       },
       fresh_states([NewInit, NewFinal], [Vs0, Vs]),
       localize_auto(Auto10, Auto1, I1, F1, Vs1),
       localize_auto(Auto20, Auto2, I2, F2, Vs2),
       merge_states(F1, F2, F),
       merge_states(Auto1.initial, Auto2.initial, I),
       skips_states(Auto1.skips, I1, States1),
       skips_states(Auto2.skips, I2, States2),
       collect_lists(Auto1.epses, States2, merge_eps_(left), [], Es1),
       collect_lists(Auto2.epses, States1, merge_eps_(right), Es1, Es),
       collect_lists(Auto1.skips, Auto2.skips, merge_skips_(F1, F2), [], Skips),
       collect_lists(Auto1.transitions, Auto2.skips, 
                     merge_trans_skip_(left), [], Trans1),
       collect_lists(Auto2.transitions, Auto1.skips, 
                     merge_trans_skip_(right), Trans1, Trans2),
       collect_lists(Auto1.transitions, Auto2.transitions, 
                        merge_trans_, Trans2, Trans).

comp_aut(iter(P), Auto)
   --> current_vars(Vs),
       comp_aut(P, Auto0),
       replace_vars(_,Vs),
       {
         sources_target_acc_epses(Auto0.final, Auto0.initial, Auto0.epses, Es),
         Auto = Auto0.put([epses=Es])
       }.

comp_aut(iter(P, Event, V), Auto)
--> 
    current_vars(Vs0),
    comp_aut(P, Auto0),
    {ord_add_element(Vs0, V, Vs)},
    fresh_states([IterInit, IterFinal], [Vs0, Vs]),
    event_fresh(Event, EventFresh0),
    event_fresh(Event, EventFresh),
    event_fresh(Event, EventFresh2),  %1
    term_trans_goals(Event, EventT, GoalList0),
    {
       EventT =.. [Type|ExprList],
       maplist(init_expr, ExprList, InitList),
       InitEvent =.. [Type|InitList],
       frame_state_push(InitEvent, Auto0.initial, I),
       maplist(frame_state_push(EventFresh0), Auto0.final, FinalN),
       frame_state_push(EventFresh, Auto0.initial, NextIter),
       EventFresh0 =.. [_|Xs0],
       EventFresh =.. [_|Xs],
       EventFresh2 =.. [_|Xs2], %2
       maplist(update_goal, ExprList, Xs0, Xs, UpdGoalList),
       maplist(finalize_goal, ExprList, Xs, Xs2, FinGoalList), %3
       append(GoalList0, UpdGoalList, GoalList),
       append(GoalList, FinGoalList, GoalList2), %4
       glist_goals(GoalList, Goals),
       glist_goals([V=EventFresh2|GoalList2], GoalsFinal), %5 (modified)
       %glist_goals([V=EventFresh|GoalList], GoalsFinal),
       sources_target_cond_acc_epses(FinalN, NextIter, Goals, 
                                     [(eps(IterInit, I) :- true)|Auto0.epses], 
                                     Epses0),
       sources_target_cond_acc_epses(FinalN, IterFinal, 
                                     GoalsFinal, Epses0, Epses),
       Auto = Auto0.put([epses=Epses, initial=IterInit, final=[IterFinal]])
    },
    replace_vars(_, Vs).      


comp_aut(filter(P, Cond), Auto)
   --> 
       comp_aut(P, Auto0),
       current_vars(Vs),
       fresh_state(S, Vs),
       cond_trans(Cond, C),
       {
         sources_target_cond_acc_epses(Auto0.final, S, C, Auto0.epses, Es),
         Auto = Auto0.put([epses=Es, final=[S]])
       }.


comp_aut(unless(P, event(Type, V), Cond), Auto1)
   -->
       comp_aut(P, Auto),
       cond_trans(#\ Cond, C),
       {
          maplist(mod_skip(Type, V, C), Auto.skips, Skips),
          Auto1 = Auto.put([skips=Skips])
       }. 

comp_aut(P within DT,  auto{
   transitions: Trans,
   epses: [(eps(NewInit, I) :- true)|Epses],
   skips: Auto0Skips,
   initial: NewInit,
   final: [NewFinal]
}) --> 
       current_vars(Vs0),
       comp_aut(P, Auto0),
       current_vars(Vs1),
       fresh_states([NewInit, NewFinal], [Vs0, Vs1]),
       fresh_vars([T0, T1, X]),
       {
         Auto0Skips = Auto0.skips,
         win_state_push(w(T0, a), Auto0.initial, I),
         maplist(win_state_push(w(T0, X)), Auto0.final, FinalN),
         sources_target_acc_epses(FinalN, NewFinal, Auto0.epses, Epses),
         maplist(window_trans(T0, T1, X, DT), Auto0.transitions, Trans)
       }.


/*
   Asserting compiled automaton.
*/

assert_trans((trans(V, Type, S0, S1) :- G))
   :- assertz((so_auto_cp:trans(S0, V, S1) :- event_type(V, Type), G)).

assert_trans((eps(S0, S1) :- G))
   :- assertz(so_auto_cp:eps(S0, S1):-G).

assert_final(Out, S)
   :- assertz(so_auto_cp:final(S, Out)).

assert_skip(skip(S, V, L))
   :- assertz(
         so_auto_cp:skip(S, X)
            :- skippable(X, V, L)
      ).

/*
assert_skip(skip(S, V, L))
   :- maplist(assert_exceptional_skip(S, V), L),
      ((L = []) 
         -> assertz(so_automaton:skip(S, V)) ; 
            assertz(so_automaton:skip(S, V) :- event_notof_types(V, L))).

assert_exceptional_skip(S, V, Type-Cond)
    :- assertz((so_automaton:skip(S, V) :- event_type(V, Type), Cond)).
*/

assert_regular(Id, Select0)
    :-  numbervars(Select0, 0, M0),
        Select0 = select(In0, Out0, Pattern),
        In0 =.. [_|Vs],
        length(Vs, NVs),
        compile_query_pure(Id, Pattern, M0, Vs, Auto0),
        varnumbers(select(In0, Out0, Auto0), Select),
        writeln(Select),
        Select = select(_, Out, Auto),
        maplist(assert_trans, Auto.transitions),
        maplist(assert_trans, Auto.epses),
        maplist(assert_skip, Auto.skips),
        Auto.initial =.. [Sid|_],
        assertz((
           so_auto_cp:initial(Id, Input, Init) 
               :- Input =.. [_|Args],
                  length(Args, N),
                  N #= NVs,
                  Init =.. [Sid, [], []|Args]
        )),
        maplist(assert_final(Out), Auto.final),
        !.
