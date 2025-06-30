(** * Tutorial Ltac2 : Type of Tactics and Thunking

  *** Authors
  - Thomas Lamiaux
  - Josselin Poiret

  *** Summary

  This tutorial contains a small tutorial explaining the type of tactics in Ltac2,
  and how to manipulate them using thunking.
  This is meant to be completed into a first introduction to Ltac2.

  *** Table of content

  - 1. Types of Tactics in Ltac2, and Thunks

  *** Prerequisites

  Disclaimer:
    - This is meant to be completed into a first introduction to Ltac2.

  Needed:

  Installation:
  - Ltac2 and its core-library are available by default with Rocq

*)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Printf.

(** 1. Types of Tactics in Ltac2, and Thunks

  Usual tactics like [assumption] or [left] are notations for Ltac2 functions.
  They modify  the proof state through side effects, such as modifying
  hypotheses or resolving an existential variable.
  They do not produce Ltac2 value, like an integer [int] of Ltac2, and are
  hence of type [unit].

  Since tactics or raising exceptions have side effects, we have to keep in mind
  when things are evaluated as side-effects are computed at evaluation.
  Ltac2 is a call-by-value language.
  This means that in Ltac2 the arguments of a function are evaluated before
  the body of the function.

  Being call-by-value is important for a functional programming language like Ltac2
  to be predictable and intuitive.
  However, this has an important side effect on manipulating tactics.
  If we pass the tactic [fail] -- that corresponds to [Control.zero (Tactic_failure None)]
  which stops computation and trigger backtracking --
  **as is** to a Ltac2 function, it will be evaluated first.
  As [fail] fails, the whole Ltac2 tactic will then fail, even if [fail] is not used.
  For instance, consider a function ignoring its arguments, and doing nothing.
  Applying it directly to [fail] will fail, even though it should do nothing.
*)

Ltac2 bad_ignore (bad_tac : unit) : unit := ().

Goal 0 = 0.
  Fail bad_ignore fail.
Abort.

(** Similarly, the definition of [let in] gets evaluated before its body,
      leading to potential failure even if the body is not used.

    For instance, in the following example [let] is evaluated first, raising an
    exception before we have a chance to print.
*)
Goal False.
  Fail let my_fail := fail in
       printf "Hello!"; my_fail.
Abort.

(** To prevent eager evaluation of terms with side effects, we need to turn them into functions.
    This way, they are only evaluated when applied, as non-applied functions are
    already fully evaluated in call-by-value languages.

    As we don't have anything else to pass to it, the only way to make a function
    out of a term [t : 'a] is to add an extra-argument of type [unit],
    i.e. to turn it into [fun () => t].
    In particular, it means that to manipulate tactics, Ltac2 functions must
    takes arguments of type [unit -> unit].

    This is a general technique in functional languages with side-effects called “thunking”:
    we have a “thunk” (a function [unit -> 'a]) that will be “forced” (called with `()`)
    later.

    As we can check with this technique, previous examples do behave as expected.
*)

Ltac2 good_ignore0 (tac : unit -> unit) : unit := ().

Goal (0 = 0).
  (* succeeds doing nothing  *)
  good_ignore0 (fun () => fail).
Abort.

Goal False.
  (* "Hello" is printed before failing *)
  Fail let my_fail := fun () => fail in
       printf "Hello!"; my_fail ().
Abort.

(** While this works, no one wants to write "thunk" by hand in proof scripts.
    Thankfully, there is an easy not to have to. It suffices to define a
    <a href="https://rocq-prover.org/doc/V9.0.0/refman/proof-engine/ltac2.html#abbreviations">Ltac2 Abbreviation</a>,
    a simple kind of notations, that directly inserts the thunks around tactics for us.
    For instance, for [good_ignore], we declare an abbreviation with the same
    name that takes a tactic as argument.
*)

Ltac2 Notation good_ignore := good_ignore0.

(** Note, that, when using general notations and not just abbreviations,
    we have to specify ourselves which arguments are "thunk".

    It is then possible to write clean proof script as usual, while having a
    meta-programming language with a clear semantics, opposite to Ltac1.
*)

Goal 0 = 0.
  good_ignore fail.
Abort.
