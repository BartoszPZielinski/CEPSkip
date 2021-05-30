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

pattern(1, select(in, out(X), 
       event(g, X) then filter(event(g, Y), ref(X, c) #= ref(Y, c))
)).

pattern(2, select(in, out(X, Y), 
       event(g, X) then unless(
           filter(event(g, Y), ref(X, c) #= ref(Y, c)),
           event(f, Z),
           ref(Z,a) #= ref(X, c)
       )
)).

pattern(3, select(in(X, Y), out,
    filter(event(f, Z), (ref(Z, time) #> ref(X, time), ref(Z, time) #< ref(Y, time)))
)).

compile_pattern(I)
    :- pattern(I, Select),
       write('Compiling pattern '), writeln(I),
       assert_regular(I, Select),
       writeln('Pattern compiled').

:- compile_pattern(_), false ; true.