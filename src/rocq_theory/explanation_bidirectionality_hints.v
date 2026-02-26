(** * Bidirectionality Hints

  *** Summary

  An explanation of bidirectionlity hints.
  After presenting the requisite background on bidirectional typing and
  existential variables in Rocq, we will see how bidirectionality hints affect
  type checking of function applications, and we will illustrate with simple
  examples.

  *** Contents

  - 1. Bidirectional typing
  - 2. Bidirectional typing and existential variables
  - 3. Bidirectionality hints
  - 4. Examples

*)

(**
Before we explain what bidirectionality hints are,
we must first understand some basics of how type checking works in Rocq.

** 1. Bidirectional typing

Rocq uses bidirectional typing, an approach to type systems that interleaves
type checking with type inference. A bidirectional type system replaces the
usual typing judgement [e : T] with two judgements: _type checking_
[e ◃ T] where [T] is an input and _type inference_ [e ▹ T]
(also called _type synthesis_ in the literature) where [T] is an output.
Making inputs and outputs explicit enables an algorithmic interpretation of the
typing rules: a bidirectional type system is a way to present a type checking
and a type inference algorithm.

Function application is usually associated with a rule for type inference ([▹]):

[[[
f ▹ forall (x : A), B x      a ◃ A
----------------------------------- app-infer
              f a ▹ B a
]]]

To infer the type of an application [f a]:

- 1. _infer_ the type of the function [f] ([f ▹ forall (x : A), B x]),
    usually [f] is a constant whose type is known from its definition.
- 2. _check_ the arguments [a] against the argument type [A].
- 3. output the result type [B a] as the _inferred_ type for [f a].

What if we want to check with a type, rather than infer it?
The following subsumption rule turns inference ([▹]) into checking ([◃]):
to check that [e] has type [T] ([e ◃ T]),
infer a type [T’] ([e ▹ T’]), then _unify_ [T’] with [T]
([T’ ≡ T]).

[[[
e ▹ T’     T’ ≡ T
----------------- infer-check
      e ◃ T
]]]

(Here we gave the subsumption rule using a type equality,
or rather _unification_ ([T’ ≡ T]).
A more general variant of the subsumption rule uses subtyping instead,
and in fact such a generalization lets us deal with coercions in Rocq.
For the rest of this explanation, we will ignore coercions
and only talk about unification ([T’ ≡ T]) to keep it simple.)

The two rules above combine into the following rule for checking an application:

[[[
f ▹ forall (x : A), B x
a ◃ A        B a ≡ T
------------------------ (1)
        f a ◃ T
]]]

To check whether the application [f a] has a given type [T]:

- 1. _infer_ the type of [f];
- 2. _check_ the argument [a] against its type [A];
- 3. _unify_ the inferred result type [B a] and the checked one [T].

** 2. Bidirectional typing and existential variables

To a first approximation, the unification judgement ([T’ ≡ T]) merely
denotes an equivalence relation between types.

This story is further complicated in Rocq by the presence of existential variables.
To avoid fully spelling out all terms, in Rocq, you can write
wildcards ([_]) instead and Rocq will try to infer them. Wildcards are replaced
with fresh existential variables with names like [?u] during pretyping.
Existential variables will then be instantiated by unification:
when a unification problem such as [?u ≡ T] is encountered, Rocq will
use this information to instantiate the variable [?u].

Thus, the typing rules above are interpreted statefully: there is a global set of
bindings for existential variables [?u := M] which is read and updated during
unification. In particular, the order in which unification judgements [T’ ≡ T]
are evaluated matters.

For example, consider the following two unification requests:
[[
?u ≡ true
0 ≡ if ?u then 0 else 1
]]

Unifying [?u ≡ true] first allows the second unification to succeed since
[if true 0 else 1] reduces to [0]. In contrast, unifying [0 ≡ if ?u then 0 else 1]
will fail if we haven't instantiated [?u] yet, because [if ?u then 0 else 1]
is stuck.

** 3. Bidirectionality hints

Bidirectionality hints indicate when unification with the result type should happen
during type-checking of a function application. By default, that happens
at the end, after having type-checked all of the arguments. This corresponds
to the type checking rule above.

A bidirectionality hint moves that unification step earlier.
Intuitively, that allows information about a function expected result type
to be propagated to type check its arguments.

For instance, to type check the application [f _ b] of a polymorphic function
[f : forall (x : A), B x -> C x], knowing that the result type is [C T]
for some [T], we may want to infer that the first argument [_] should be [T]
and check that the second argument [b] has type [B T]. However, by default,
without a bidirectionality hint, the result type [C T] will be ignored at first,
and [b] will be checked against a type [B ?x] containing less known information.

Earlier, we showed the type checking rule for a function application with one argument.
While function applications with multiple arguments [f a b] are technically
multiple nested applications [(f a) b],
for the purposes of type checking in Rocq, they are treated as a single n-ary application.
For example, the rule for type checking an application with two arguments [f a b] looks like this:

[[[
f ▹ forall (x : A), B x -> C x
a ◃ A     b ◃ B a     C a ≡ T
------------------------------- (2)
          f a b ◃ T
]]]

(For more generality, you could reformulate that typing rule with
the more dependent function type [forall (x : A) (y : B x), C x y],
and also with more arguments. We will stick to this simpler form
as our running example.)

In other words, we check whether the application [f a] has a given type [T]
following these steps:

- 1. infer the type of [f];
- 2. check the first argument [a] against its type [A] contained in the type of [f];
- 3. check the second argument [b] against its type [B a]
    (that is [B x] from the type of [f] with [x] replaced by [a]);
- 4. unify the result type [C a] and [T].

The unification of the result types is the last step by default.
That behavior can be modified using bidirectionality hints.

_Bidirectionality hints_ are declared using the [Arguments] command,
as a [&] symbol. For example:
[[
Arguments f _ & _.
]]

This hint [f _ & _] makes unification happen after type checking the first
argument, instead of at the end, resulting in the following type checking rule:

[[[
f ▹ forall (x : A), B x -> C x
a ◃ A     C a ≡ T     b ◃ B a
----------------------------- (2)
         f a b ◃ T
]]]
*)

(** ** 4. Examples *)

Section Example.

(** Let us demonstrate the difference with two examples: one does not require the hint, the other does.
  Both use the same concrete definitions for the types [A], [B], and [C] below,
  where [B] and [C] pattern match on the first argument [x : A]: *)

Let A : Type := bool.
Let B (x : A) : Type := if x then bool else nat.
Let C : A -> Type := B.

Variable f : forall (x : A), B x -> C x.

(** *)

Section Example1.

(** The expression [f _ (0 : B false) : nat] type checks without
bidirectionality hints, but fails with the hint [f _ & _]. *)

(** With no bidirectionality hint, type checking [f _ (0 : B false) ◃ nat] proceeds as follows:
- 0. generate a fresh existential variable [?x] in place of the wildcard [_];
- 1. check the first argument [?x ◃ bool]: do nothing
    (actually, [bool] gets unified with the type of [?x], which is another fresh existential variable,
    but that is not an important detail for this explanation);
- 2. check the second argument [(0 : B false) ◃ B ?x]: the type annotation gives us the inferred type [B false],
    which is unified with the checked type [B ?x], and we unify [false] with [?x] (note that this unification step happens
    even if [B] is not injective: in general, [B false ≡ B ?x] does not imply [false ≡ ?x];
    unification in Rocq is lossy, it does not aim to find most general unifiers);
- 3. unify the result types [C ?x ≡ nat]: it succeeds because we previously unified [?x] with [false].
 *)

(* No bidirectionality hint. *)
Check (f _ (0 : B false) : nat).

(** With a bidirectionality hint, type checking proceeds as follows:
- 1. check the first argument [?x ◃ bool]: same as before;
- 2. unify the result types [C ?x ≡ nat], that is [(if ?x then bool else nat) ≡ nat],
    which fails because [?x] is still unknown. *)

(* Add bidirectionality hint. *)
Arguments f _ & _.
Fail Check (f _ (0 : B false) : nat).

(** *)

End Example1.

(** *)

Section Example2.

(** The expression [f _ 0 : C false] type checks with the hint
[f _ & _] but fails without. *)

(** With no bidirectionality hint:
- 1. check the first argument [?x ◃ bool]: same as before;
- 2. check the second argument [0 ◃ B ?x]: [0] is a constant so its type can be inferred as [nat],
    which is unified with the checked type [B ?x], and that fails because [?x] is still unknown. *)

(* No bidirectionality hint. *)
Fail Check (f _ 0 : C false).

(** With the bidirectionality hint:
- 1. check the first argument [?x ◃ bool]: same as before;
- 2. unify the result types [C ?x ≡ C false], which unifies [?x ≡ false];
- 3. check the second argument [0 ◃ B ?x]: its type is inferred as [nat],
    which is unified with the checked type [B ?x],
    and that succeeds we previously unified [?x] with [false]. *)

(* Add bidirectionality hint. *)
Arguments f _ & _.
Check (f _ 0 : C false).

(** *)

End Example2.

(** *)

End Example.
