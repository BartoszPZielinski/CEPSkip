:- use_module('event_types.pl').
:- use_module('so_auto_cp.pl').
:- use_module('skip_pattern_syntax.pl').
:- use_module('skip_pattern_compiler.pl').
:- use_module(library(clpfd)).

/*
     Example: Abstract system
*/

:- encoding(utf8).

:- def_event_types([
       f(a, b, time),
       g(c, time),
       h(a, b, c, time),
       aggr1(count),
       aggr2(sum, count, max_time),
       aggr3(count, max_time),
       aggr4(sum1, sum2, max_time), 
       lambda(par),
       f1(a, time),
       f2(a, time),
       f3(a, time),
       f4(a, time),
       f5(a, time),
       f6(a, time),
       f7(a, time),
       f8(a, time),
       f9(a, time),
       f10(a, time),
       f11(a, time),
       f12(a, time),
       f13(a, time),
       f14(a, time),
       f15(a, time),
       f16(a, time),
       f17(a, time),
       f18(a, time),
       f19(a, time),
       f20(a, time)
    ]).

pattern(1,
       select(in, out(X, T), 
          event(g, X) 
               then iter(
                    unless(
                         filter(
                              event(f, Y),
                              (ref(Y, a) #= ref(X, c) #/\ ref(Y, b) #> 0)     
                         ),
                         event(f, Z),
                         (ref(Z, a) #= ref(X, c) #/\ ref(Z, b) #> 0) 
                    ),
                    aggr3(count(*), max(ref(Y, time))),
                    T
               )
       )
     ).

pattern(2, select(in(X, T, Λ), out,
     filter(
          iter(
               filter(
                    event(f, Y), 
                    (
                         ref(X, time) #< ref(Y, time)
                              #/\ ref(X, c) #= ref(Y,a)
                              #/\ ref(Y,time) #=< ref(T, max_time)     
                    )
               ),
               aggr1(count(*)),
               Z
          ), 
          ref(T, count) + ref(Λ, par) #< ref(Z, count)
     )
)).
compile_pattern(I)
     :-   pattern(I, Pattern), 
          write('Compiling pattern:'),
          writeq(Pattern),
          assert_regular(I, Pattern),
          nl,
          write('Pattern compiled').


/*
match_list(Id, L0, L, Out, Options)
   :- option(input(Input), Options, in),
      option(output(Output), Options, out),
      option(max_depth(MaxLen), Options, 20),
      option(max_time(MaxTime), Options, 1000),
      match_list(Id, L0, L, Out, Input, Output, MaxLen, MaxTime).
*/
        
run(Λ, MaxDepth,L0, R, B1-B2, [X, T])
     :- match_list(1, L0, L, B1, [output(out(X, T)), max_depth(MaxDepth)]),
        match_list(2, L, R, B2, [input(in(X, T, lambda(Λ))), max_depth(MaxDepth)]). 

timed_run(Λ, MaxDepth, L0, R, Bs, Vars)
     :- time(run(Λ, MaxDepth, L0, R, Bs, Vars)).     

:- maplist(compile_pattern, [1, 2]).
