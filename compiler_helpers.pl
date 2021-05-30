:- module(compiler_helpers, [
        frame_state_push/3,
        win_state_push/3,
        term_trans_goals//3,
        glist_goals/2,
        cond_trans//2,
        sources_target_acc_epses/4,
        sources_target_cond_acc_epses/5,
        init_expr/2,
        update_goal/4,
        finalize_goal/4,
        window_trans/6,
        mod_skip/5,
        merge_states//3,
        skips_states/3,
        localize_auto//5,
        collect_lists//5,
        merge_eps_//5,
        merge_skips_//6,
        merge_trans_skip_//5,
        merge_trans_//4
    ]).

:- use_module(library(clpfd)).
:- use_module('compiler_state.pl').

frame_state_push(Frame, S0, S)
:- S0 =.. [Sid, IterVar | Vs],
   S  =.. [Sid, [Frame | IterVar] | Vs].

win_state_push(StartWindow, S0, S)
:- S0 =.. [Sid, IterVar, WinVar | Vs],
   S  =.. [Sid, IterVar, [StartWindow|WinVar] | Vs].

/*
   Translate conditions. Extract references ref(var, field, value)
*/

term_trans_goals(
    ref(Var, Field),
    V,
    [ref(Var, Field, V)]
 ) --> fresh_var(V), !.

term_trans_goals(Cond, Trans, Goals)
   --> {
          Cond =.. [F|L], 
          dif(F, ref)
       },
       terms_trans_goals_(L, L1, Goals),
       {Trans =.. [F|L1]}.

terms_trans_goals_([],[],[]) --> [].
terms_trans_goals_([C|L],[T|L1], Gs)
--> term_trans_goals(C, T, G),
    terms_trans_goals_(L, L1, Gs0),
    {append(G, Gs0, Gs)}.

glist_goals([], true).
glist_goals([G], G).
glist_goals([G1, G2|Gs], (G1, Goals))
 :- glist_goals([G2|Gs], Goals).

cond_trans(Cond, Goals)
 --> term_trans_goals(Cond, T, Gs),
     {
       append(Gs, [T], Gs1),
       glist_goals(Gs1, Goals)
     }.

/*
   Renumbering variables
 */

renumber_var('$VAR'(N0), '$VAR'(N), '$VAR'(N0), '$VAR'(N)).
renumber_var('$VAR'(N0), _, '$VAR'(N), '$VAR'(N))
     :- N0 #\= N.
renumber_var('$VAR'(N0), '$VAR'(N), C0, C)
      :- C0 =.. [F|Args0],
         dif(F, '$VAR'),
         maplist(renumber_var('$VAR'(N0), '$VAR'(N)), Args0, Args),
         C =.. [F|Args].

/*
    Adding epses
 */

sources_target_acc_epses([], _, L, L).
sources_target_acc_epses([S|Ss], T, Acc, L)
    :- sources_target_acc_epses(Ss, T, [(eps(S, T) :- true)|Acc], L).

sources_target_cond_acc_epses([], _, _, L, L).
sources_target_cond_acc_epses([S|Ss], T, C, Acc, L)
    :- sources_target_cond_acc_epses(Ss, T, C, [(eps(S, T) :- C)|Acc], L).

/*
    Iteration helpers
 */

init_expr(sum(_), 0).
init_expr(min(_), nothing).
init_expr(max(_), nothing).
init_expr(count(*), 0).
init_expr(avg(_), a(0,0)).

update_goal(sum(E), X0, X, X #= X0 + E).
update_goal(min(E), X0, X, so_auto_cp:ext_min(X0, E, X)).
update_goal(max(E), X0, X, so_auto_cp:ext_max(X0, E, X)).
update_goal(count(*), X0, X, X #= X0 + 1).
update_goal(avg(E), X0, X, so_auto_cp:update_avg(X0, E, X)).

finalize_goal(min(_), X0, X, X #= X0).
finalize_goal(min(_), X0, X, so_auto_cp:fin_minmax(X0, X)).
finalize_goal(max(_), X0, X, so_auto_cp:fin_minmax(X0, X)).
finalize_goal(min(_), X0, X, so_auto_cp:fin_minmax(X0, X)).
finalize_goal(count(*), X0, X, X #= X0).
finalize_goal(avg(_), X0, X, so_auto_cp:fin_avg(X0, X)).

%init_expr(max(_), nothing).
%update_goal(max(E), X0, X, ext_max(X0, E, X)).

/*
    Time window helpers
 */

window_trans(T0, T1, X, DT, 
   (trans(V, Type, S0, S1) :- G), 
   (trans(V, Type, ST0, ST1) :- G, event_time(V, T1), update_time(X, T0, T1, DT))
) :- win_state_push(w(T0, X), S0, ST0),
     win_state_push(w(T0, b), S1, ST1).

/*
    Unless helpers
 */

mod_skip(Type, V0, C0, skip(S, V, L0), skip(S,  V, L))
:- renumber_var(V0, V, C0, C),
   mod_or_add_skip_rules(Type, C, L0, L).

mod_or_add_skip_rules(Type, C, [], [Type-C]).
mod_or_add_skip_rules(Type, C, [Type-C0 | L0], [Type-(C, C0) |L0]).
mod_or_add_skip_rules(Type, C, [Type0-C0 | L0], [Type0-C0 | L])
:- dif(Type, Type0),
   mod_or_add_skip_rules(Type, C, L0, L).

/*
    And helpers
 */

merge_states(S1, S2, S)
--> stack_vars(IterVar, WinWar),
    {
      S1 =.. [Sid1|_],
      S2 =.. [Sid2|_],
      term_to_atom(a(Sid1, Sid2), Sid),
      S =.. [Sid, IterVar, WinWar, S1, S2]
    }.
   
reinit_state(S0, S)
:- S0 =.. [Sid, _, _ | Vs],
   S =.. [Sid, [], []|Vs].

skipped_state(skip(State, _, _), State).

state_in(S0, [S1|_])
   :- S0 =.. [F|_],
      S1 =.. [F|_].
state_in(S0, [S1|L])
   :- S0 =.. [F1|_],
      S1 =.. [F2|_],
      dif(F1, F2),
      state_in(S0, L).

skips_states(Skips, I, States)
   :- maplist(skipped_state, Skips, States0),
      (state_in(I, States0) 
         -> States=States0 
          ; States = [I|States0]).


localize_auto(Auto0, Auto, I, F, Vs)
   --> stack_vars(IterVar, WinWar),
       fresh_state(F, Vs),
       fresh_vars([NewIter, NewWin, V]),
       {
         sources_target_acc_epses(Auto0.final, F, Auto0.epses, Epses),
         Skips = [skip(F, V, [])|Auto0.skips],
         Auto1 = Auto0.put([final=[F],
                            epses=Epses,
                            skips=Skips]),
         renumber_var(IterVar, NewIter, Auto1, Auto2),
         renumber_var(WinWar, NewWin, Auto2, Auto3),
         I = Auto3.initial,
         reinit_state(I, NewInitial),
         Auto = Auto3.put([initial=NewInitial])
    }. 

collect_lists([], _, _, Out, Out) --> [].
collect_lists([L0|Ls0], Ls1, F, Buf0, Out)
   --> collect_list(Ls1, L0, F, Buf0, Buf1),
       collect_lists(Ls0, Ls1, F, Buf1, Out).
collect_list([], _, _, Out, Out) --> [].
collect_list([L1|Ls1], L0, F, Buf0, Out)
   --> call(F, L0, L1, Buf0, Buf1),
       collect_list(Ls1, L0, F, Buf1, Out).

%
merge_eps_(Dir, (eps(S0, S1) :- G), S, Buf, [(eps(Sm0, Sm1) :- G)|Buf])
--> merge_states(Dir, S0, S, Sm0),
    merge_states(Dir, S1, S, Sm1).

merge_states(left, S1, S2, S)
--> merge_states(S1, S2, S).
merge_states(right, S1, S2, S)
--> merge_states(S2, S1, S).

%
merge_skips_(F1, F2, skip(S1, V1, L1), skip(S2, V2, L2),  Buf, Buf1)
--> {S1=F1, S2=F2} -> {Buf1 = Buf} ; (
      merge_states(S1, S2, S),
      {
         renumber_var(V1, V2, L1, L11),
         merge_specs(L11, L2, L),
         Buf1 = [skip(S, V2, L)|Buf]
      }
). 

merge_specs([], Spec, Spec).
merge_specs([Pair|Spec0], Spec1, Spec)
:- merge_spec(Spec1, Pair, Spec2),
   merge_specs(Spec0, Spec2, Spec).

merge_spec([], Pair, [Pair]).
merge_spec([Type-Cond0|Spec0], Type-Cond, [Type-(Cond0, Cond)|Spec0]) 
:- !.
merge_spec([Type0-Cond0|Spec0], Type-Cond, [Type0-Cond0|Spec])
:- dif(Type0, Type),
   merge_spec(Spec0, Type-Cond, Spec).

%
merge_trans_skip_(
   Dir,
   (trans(V, Type, S0, S1):-G), 
   skip(S2, V1, L), 
   Buf,
   [(trans(V, Type, Sm0, Sm1):-C, G)|Buf]
) --> merge_states(Dir, S0, S2, Sm0),
      merge_states(Dir, S1, S2, Sm1),
      {
         type_spec_cond(Type, L, C0),
         renumber_var(V1, V, C0, C)
      }.

type_spec_cond(_, [],  true).
type_spec_cond(Type, [Type-C|_], C) :- !.
type_spec_cond(Type, [Type1-_|L], C)
   :- dif(Type, Type1),
      type_spec_cond(Type, L, C).

%

merge_trans_(
   (trans(V1, Type1, S10, S11) :- G1),
   (trans(V2, Type2, S20, S21) :- G2),
   Buf, Buf1
) --> {Type1 = Type2} -> (
         merge_states(S10, S20, S0),
         merge_states(S11, S21, S1),
         {Buf1 = [(trans(V2, Type2, S0, S1) :- V1=V2, G1, G2)|Buf]}
     ) ; {Buf1 = Buf}. 


