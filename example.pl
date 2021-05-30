:- use_module('event_types.pl').
:- use_module('so_auto_cp.pl').
:- use_module('skip_pattern_syntax.pl').
:- use_module('skip_pattern_compiler.pl').
:- use_module(library(clpfd)).

/*
     Example: Traffic control
*/

:- encoding(utf8).

:- def_event_types([
          /* The bus id enters/leaves stop identified by stop_id.
             the difference between scheduled time and current time is δ_schedule
             current time is time */
          stop_enter(id, stop_id, δ_schedule, time),
          stop_leave(id, stop_id, δ_schedule, time),
          /* Events emitted at abrubt acceleration/deceleration of
             bus id at time time */
          abrupt_accel(id, time),
          abrupt_decel(id, time),
          /* The bus id made a sharp turn to dir (left/right) at time time */
          sharp_turn(id, dir, time),
          /* Driver logs in/out to the bus */
          driver_in(id, drv_id, time),
          driver_out(id, drv_id, time),
          /* The bus id reports max, min, and avg velocity between times start_time 
             and time. */
          velocity(id, max, min, avg, start_time, time),
          /* The bus id reports location location_id at time time.*/
          location(id, location_id, time),
          /* Event used for aggregation only */
          agg(cnt)
    ]).

   pattern(1, select(in, out(Se, K),
      filter(event(stop_enter, Se), ref(Se, δ_schedule) #>= 120) then unless(
         unless(
            filter(
               event(stop_leave, Sl), 
               ref(Sl, id) #= ref(Se, id) #/\ ref(Se, stop_id) #= ref(Sl, stop_id)
            ),
            event(stop_leave, L),
            ref(L, id) #= ref(Se, id)
         ), 
         event(driver_in, Di),
         ref(Di, id) #= ref(Se, id)
      ) then unless(
            filter(
               iter(
                  filter(
                     event(abrupt_accel, E) or 
                     event(abrupt_decel, E) or 
                     event(sharp_turn, E),
                     ref(E, id) #= ref(Se, id) 
                  ),
                  agg(count(*)), 
                  I
               ), ref(I, cnt) #>= 3
            ) then filter(
                  event(stop_enter, K), ref(K, id) #= ref(Se, id)
            ),
            event(stop_enter, T),
            ref(T, id) #= ref(Se, id)
      )
   )).

pattern(2, select(in(Se, K), out, 
   filter(
      event(driver_in, D), 
      ref(D, id) #= ref(Se, id) #/\ 
      ref(D, time) #> ref(Se, time) #/\
      ref(D, time) #< ref(K, time)
   )
)).

compile_pattern(I)
:-   pattern(I, Pattern), 
     write('Compiling pattern:'),
     writeq(Pattern),
     assert_regular(I, Pattern),
     nl,
     write('Pattern compiled').

run(MaxDepth,L0, R, B1-B2, [X, T]) 
:- match_list(1, L0, L, B1, [output(out(X, T)), max_depth(MaxDepth)]),
   match_list(2, L, R, B2, [input(in(X, T)), max_depth(MaxDepth)]).      

:- maplist(compile_pattern, [1, 2]).