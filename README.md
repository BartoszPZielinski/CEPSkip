# CEP Pattern Recognizer and Compiler With Skipping Constraints

## Requirements
The code was tested only with SWI Prolog (it may not work with other Prolog environments as it uses some non-standard libraries. Also module systems differ between Prolog interpreters).

The execution of the code should not depend on the operating system (it was tested on MacOS X and Windows 10) as it does not use any operating system specific libraries.

## Syntax of the pattern language
The pattern language uses the following constructs:

* `empty` pattern matches empty string of events.
* `event(T,X)` matches an event of type `T` and binds it to `X`
* `iter(P)` matches repetitions of `P`.
* `iter(P, f(h₁(E₁),…,hₐ(Eₐ)), X)` matches repetitions of `P`, and binds `X` to an event `f(v₁,…,vₐ)` where `v₁` is the result of aggregating with `hᵢ` the values of expression `Eᵢ`. I is assumed that event schema contains the definition of an event type of the form `f(a₁,…,aₐ)` so that we can later refer to `vᵢ` as `ref(X, aᵢ)`.
* `P₁` or `P₂` matches events matched either by `P₁` or `P₂`.
* `P₁` and `P₂` matches events matched by both `P₁` and `P₂`.
* `P₁` then `P₂` matches `P₁` followed by `P₂`.
* `filter(P, C)` matches `P` if it satisfies condition `C`.
* `unless(P, event(T, X), C)` matches string `S` matched by `P` if in `S` there does not occur an event of type `T` not explicitly matched in `P` which satisfies condition `C`.
* `P within Δ` matches `P` if all events matched by `P` occur within interval `Δ`.

**Remark 1**: Currently we implement standard aggregate functions `sum(E)`, `min(E)`, `max(E)`, `avg(E)`, `count(*)`.

**Remark 2**: The only numerical values allowed are integers and all conditions must use predicates from `library(clpfd)`.

A pattern is passed to the compiler always as a full pattern, i.e., as a term of the form `select(Input, Output, Pattern)`, where `Pattern` is a pattern (constructed with functors as above) and `Input` and `Output` are terms of the form `in(X₁,…,Xₑ)` and `out(Y₁,…,Yₐ)`, respectively, where

* X₁,…,Xₑ are distinct variables which must include all free variables of `Pattern`,
* Y₁,…,Yₐ are distinct variables which must contain only variables bound by `Pattern`.

It remains to describe the binding structure of patterns. First we describe (by recursion on the structure of the pattern) the set of variables bound by a pattern:

* `empty` binds nothing
* `event(T, X)` binds `X` (to the matched event of type `T`)
* `iter(P)` binds nothing.
* `iter(P, f(h₁(E₁),…,hₐ(Eₐ)), X)` binds only `X`
* `P₁ or P₂` binds variables bound by both `P₁` and `P₂`. Since only one of the two alternatives is actually matched there is no possibility of conflict
* `P₁ and P₂` and `P₁ then P₂` binds variables bound by either `P₁` or `P₂`. Bindings from `P₂` shadow bindings from `P₁`
* `filter(P, C)`, `unless(P, Event(T,X), C)` and `P within Δ` bind variables bound by `P` (in particular `X` is not visible outside).

Let us now describe shadowing and (internal) scope of variable bindings. Variables are read in conditions and in aggregation expressions. We have

* `empty` and `event(T,X)` cannot contain conditions or aggregation expressions so there is nothing to describe here.
* For `iter(P)` and `P within Δ` scope of variables is the same as in `P`
* Consider `iter(P, f(h₁(E₁),…,hₐ(Eₐ)), X`). `X` is not visible in `P` or expressions `Eᵢ`. Expressions `Eᵢ` are in the scope of variables bound by `P` which take precedence (shadow) external binding of identically named variables.
* In case of `P₁ or P₂` and `P₁ and P₂` neither bindings provided by `P₁` are visible in `P₂` nor bindings provided by `P₂` are visible in `P₁`.
* In case of `P₁ then P₂` bindings provided by `P₂` are not visible in `P₁`. However, bindings provided by `P₁` are visible in `P₂`. In case of conflict inside `P₂` variables bound inside `P₂` shadow those bound by `P₁`.
* In case of `filter(P, C)` condition `C` is in the scope of variables bound by `P` and bindings provided by `P` take precedence (shadow) external ones.
* In case of `unless(P, Event(T,X), C)` `C` is in the scope of `X` but not of variables bound by `P`.

The compilation function requires that there is no shadowing of variables. Naively, it would seem to be sufficient to forbid binding the same variable in two distinct places in the same pattern. However, since the alternative (`P₁ or P₂`) binds variables bound in both subpatterns we have to permit repetition of bindings in alternative subpatterns if they are not shadowed. A pattern which contains only minimal repetition of bindings (in the alternative subpatterns) is said to satisfy the unique variable property

## Description of files (modules)

### event_types.pl

The module `event_types` defines two important functors: `def_event_type/1` and `def_event_types/1` which accept as a single argument either, respectively, a single declaration of an event type or a list of such declarations. The functors assert associated definitions of `ref/3` and `event_type/2` functors (also exported by the module). The role of the generated functors is explained below. Finally the module also defines functors `event_time/2` (returning timestamp of an event), and `update_time/4` which is used by generated automaton and not by the user.

Recall that events are represented as Prolog terms of the form

```
⟨event type⟩(⟨attr_value₁⟩, ⟨attr_value₂⟩, …)
```

where `⟨event type⟩` plays the role of functor, and arguments are the event’s attributes. Event schema is a list of terms of the form
```
⟨event_type⟩(⟨attr_name₁⟩, ⟨attr_name₂⟩, …)
```

with no two terms with the same functor. Declaration such as the one above means that events of type `⟨event_type⟩` have attributes with names `⟨attr_name₁⟩`, `⟨attr_name₂⟩`, ….. Event

```
⟨event type⟩(⟨attr_value₁⟩, ⟨attr_value₂⟩, …)
```

has type `⟨event type⟩` and its argument of name `⟨attr_nameᵢ⟩` has value `⟨attr_nameᵢ⟩` for i∈{1, 2, …}.

If `X` is an event with an attribute a then our pattern language we refer to the value of this attribute as `ref(X, a)`. During compilation of patterns such terms are replaced by fresh variables (say `Y` for the sake of example) and additional goals of the form `ref(X, a, Y)` are added. The goal `ref(X, a, Y)` is satisfied when the attribute a of event `X` has value `Y`.

To check the type of an event one can use predicate `event_type/2`: The goal
```
event_type(⟨event⟩, ⟨type⟩)
```

is satisfied when `⟨event⟩` has type `⟨type⟩`.

### so_auto_cp.pl

This module defines a runtime for an automaton recognizing "skipping" patterns on lists. To define an automaton (or rather a family of automatons) itself, a user needs to provide definition for the following five predicates ( the first argument of the first predicate is an identifier which distinguishes between distinct, simultanously defined automatons):

* `initial(Id, Input, I)` : `I` is an initial state for automaton Id. Input is a term of the form `in(E₁, …, Eₐ)` (the actual functor may depend on the definition of the automaton), where `E₁, …, Eₐ` are bound to variables in the initial state `I`.
* `final(F, Output)` : `F` is a final state. Output is a term of the form `out(X₁,…,Xₐ)` (the actual functor may depend on the definition of the automaton) where `X₁,…,Xₐ` are variables which get bound to the values of selected event variables associated with the final state `F`.
* `trans(S0, E, S1)` : automaton can move, after consuming an event `E` from state `S0` to state `S1`.
* `eps(S0, S1)` : automaton can do an ϵ-move from `S1` to `S2`,
* `skip(S, E)` : automaton can skip event `E` when in state `S`.

To run the automaton use `match_list/5` which is the sole functor exported by module `so_automaton`. More precisely, the goal
```prolog
match_list(Id, L, R, Out, Options)
```

is satisfied iff the automaton identified by `Id` recognizes a list `L` which it rewrites into `R` and `Out` is a bitmap (a list of 0's and 1's) of the same length as `R` and such that it has 1's at the positions corresponding to the positions in `R` of events actually matched by the automaton (consumed in ordinary transitions) and 0's at positions corresponding to events which were skipped. `Options` is a list of options:

* `input(Input)`: (default `in`)
* `output(Output)` (default `out`)
* `max_depth(MaxLen)` (default 20): Only `MaxLen` of events will be consumed. This limits the depth of search.
* `max_time(MaxTime)` (default 1000): this is workaround limitations of Prolog integer constraint solver which without limiting the domain to finite subset cannot recognize contradiction in  `A<B ∧ B<A`.
 
 `Input` and `Output` have the same meaning as above, i.e., when executing the goal `Input` gets passed as a second argument to `initial/3` and `Output` is passed as the second argument to `final/2`.

### skip_pattern_syntax.pl

Module `skip_pattern_syntax` exports, aside from binary operators `or`, `and`, `then` and `within` which are used in the patterns, also some predicates which check the properties of patterns and convert patterns. Below we give a list:

* `pattern_binds/2`: Given a pattern P a goal `pattern_binds(P, V)` binds to `V` the (ordered) list of all variables bound by `P`
* `closed/2`: Given a pattern P a goal `closed(P, V)` is satisfied iff `P` is closed and `V` is the ordered list of variables bound by `P` (i.e., the same set as `pattern_binds/2` binds).
* `is_unique_pattern/1`: The goal `is_unique_pattern(P)` is satisfied iff a pattern `P` has a unique variable property.
* `make_pattern_unique/2`: Given a pattern `P0` the goal `make_pattern_unique(P0, P)` binds to a variable `P` the pattern equivalent to `P0`, but with fresh variables and satisfying the unique variable property.

Note that while predicates `pattern_binds/2`, `closed/2`, and `is_unique_pattern/1` do not make any assumptions about how the event variables are represented in the pattern passed as an argument (actual Prolog variables or any other terms, it does not matter), but `make_pattern_unique/2` requires for correct execution that the pattern passed as a first argument has event variables represented by actual Prolog variables (and the resulting pattern bound to the second argument represents event variables as Prolog variables as well). This is not checked in the goal, so it may lead to difficult to find errors.

### skip_pattern_compiler.pl

Module `skip_pattern_compiler` defines predicates which compile patterns into automatons (described earlier). The module exports a single predicate:
`assert_regular/2`: Given an identifier `Id` (which can be any term) and a pattern `P` the goal `assert_regular(Id, P)` asserts (into the user module) the predicates `initial/3`, `final/2`, `trans/3`, `eps/2` and `skip/2` (see the section on `so_automaton.pl` ).
For debugging purposes `assert_regular/2` prints to the terminal internal representation of the compiled automaton. The automaton is represented as the following dict:

```
  auto{
    transitions: [trans(V, Type, S0, S1):-G, ...],
    epses: [eps(S0, S1):-G, ...],
    skips: [skip(S, V1, event_specs)],
    initial: S,
    final: [S, ...]
}
```

where

* `transitions` is a list of terms (representing transitions) of the form `trans(V, Type, S0, S1) :- G`, where `V` is an event variable bound to an event of type `Type` consumed in the transition. `S0` is the source state of transition and `S1` is the target state of the transition. Finally, `G` are additional constraints of the transition
* `epses` is a list of terms of the form `eps(S0, S1):-G`, where `G` is a condition under which an automaton can ϵ-move from `S0` to `S1`
* `initial` is the initial state of the automaton,
* `final` is the list of the final states of the automaton,
* `skips` is the list of terms of the form `skip(state, variable, event_specs)` with at most one such term for each state state, where event_specs is a list of pairs of the form `type-condition`. An event `E` is skippable in the state state iff its type `T` is either not on the list `event_specs` or `event_specs` contains the pair `T-C` and then the condition `C` is satisfied. The variable `variable` is used to refer to event under consideration in all the conditions in `event_specs`.

### compiler_state.pl

The file contains definitions of internal predicates assisting in compilation proces. They are not to be used directly by the user.

### compiler_helpers.pl

The file contains definitions of internal predicates assisting in compilation proces. They are not to be used directly by the user.

### skippable.pl

This file contains definition of variable attribute `skippable` and associated hooks which permits constraint reasoning about types of events an unbound variable cannot be bound to. This module exports a single predicate `skippable/3`, where:

* if `Event` is a variable, `V` is a fresh variable and `Pairs` is a list of pairs ⟨type, condition⟩, with condition constraining `V` then `skippable(Event, V, Pairs)` adds to `Event` a constraint `skip(V, Pairs)` which declares that `Event` is either not of one of types mentioned in `Pairs`, or it satisfies the condition associated to the type.
* if `Event` is not a variable than the skippability condition is checked.

### example.pl
This file contains specifications and patterns for the city transport traffic management. To run the examples (as it is explained in the next section) one needs to simply consult this file into Prolog interpreter (it loads all the other files as modules), and then give appropriate commands which answer questions about aspects of the system.

### skip_example.pl

Another example.

# improvement_test_new.pl

This file contains specification and example patterns for the efficiency test and comparisons with the original implementation. The specification is deliberately abstract (there are no real-life stories behind it).

## How to run examples from example.pl, skip_example and improvement_test.pl

In order to run the examples from the paper first cd into the folder with Prolog files and run the interpreter with the command:

```bash
swipl example.pl
```

or

```bash
swipl improvement_test.pl
```

or

```bash
swipl skip_example.pl
```

Either of the file loads all the necessary modules. Then a given event schema is compiled. Next, a predicate `pattern(Id, Pattern)` is defined where `Id` is a numeric identifier and `Pattern` is an example (full) pattern. In each of the files several example patterns are defined. All of the patterns are automatically compiled when loading the files. 

Then, in order to test examples use the `match_list/5` predicates from the
`so_auto_cp.pl` module, e.g., 
```prolog
match_list(1, L0, L, B1, [output(out(X, T)), max_depth(30)]),
   match_list(2, L, R, B2, [input(in(X, T)), max_depth(30)]).
```

In order to use the timing example from the paper
load `improvement_test_new.pl` 
and then use predicate of the form
```prolog
  run(Λ, MaxDepth,L, R,B1-B2, [X, T]) 
```
where `Λ` is the second pattern parameter, Depth is the maximal length of considered list, `L`, `R`, `B1`, `B2` and `X`, `T` are variables (`R` will be the generated solution).

We used the following calls to get measurement points:

```prolog
timed_run(1, 20, L, R, B1-B2, [X, T]).
timed_run(2, 20, L, R, B1-B2, [X, T]).
timed_run(3, 20, L, R, B1-B2, [X, T]).
timed_run(4, 20, L, R, B1-B2, [X, T]).
timed_run(5, 20, L, R, B1-B2, [X, T]).
timed_run(10, 80, L, R, B1-B2, [X, T]).
timed_run(30, 80, L, R, B1-B2, [X, T]).
```
