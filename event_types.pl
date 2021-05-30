:- module(event_types, [
        def_event_type/1, 
        def_event_types/1,
        ref/3,
        event_type/2,
        event_time/2,
        update_time/4
   ]).

:- use_module(library(varnumbers)).
:- use_module(library(clpfd)).

update_time(a, T0, T1, _)
   :- T0 #= T1.
update_time(b, T0, T1, DT)
   :-  T1 #< T0 + DT.

:- dynamic ref/3.
:- dynamic event_type/2.

event_time(Event, Time)
   :- ref(Event, time, Time).

 args_vars_next([],[], _).
 args_vars_next([_|Args], ['$VAR'(Next0)|Vars], Next0)
     :- Next #= Next0 + 1,
        args_vars_next(Args, Vars, Next).

assert_ref_args([], _, _).
assert_ref_args([Arg|Args], Event0, N0)
     :- varnumbers(ref(Event0, Arg, '$VAR'(N0)), R),
        assert(R),
        N #= N0 + 1,
        assert_ref_args(Args, Event0, N).

def_event_type(ET)
     :- ET =.. [Type|Args],
        args_vars_next(Args, Vars, 0),
        Event0 =.. [Type|Vars],
        varnumbers(Event0, Event),
        assert(event_type(Event, Type)),
        assert_ref_args(Args, Event0, 0).

def_event_types(ETs)
     :- maplist(def_event_type, ETs).
