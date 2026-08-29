(** * Tutorial Easy

  *** Summary
  In this tutorial, we give an general idea of what the tactic [easy] and [now]
  does and its uses.

  *** Table of content
  - 1. Basic definitions and reasoning
  - 2. With clauses
  - 3. Where clauses

  *** Prerequisites

  Needed:
  - We assume basic knowledge of Coq

  Installation:
  - Easy is available by default in Coq
*)

Require Import List. Import ListNotations.

(** 1. Introduction

    The tactic [easy] is an automation tactic designed to solve a wide class of "trivial" goals.
    It does so by suitably combining different basic automation tactics like
    [reflexivity] or [contradiction], that are designed to solve very specific
    kind of trivial goals.

    Intuitively, [easy] tries to solve the goal by repeatedly: introducing
    the head hypothesis, simplifying conjunction in it and checking it
    for inconsistencies, and then tries to solve the goal using a set of
    basic automation tactic.
    If it does not manages to solve the goal, [easy] fails.

    As it can be seen below, it manages to find both contradiction and do not get
    stuck on introduction or conjunction:
*)

Goal forall (n m : nat), n = 0 -> S m = 0 -> 0 = 1.
  easy.
Qed.

Goal forall (n m : nat), n = 0 /\ m = 0 -> n = 0.
  easy.
Qed.

(** Using [easy] systematically has different advantages:
    1. It enables to solve automatically a variety of trivial goals without having
      to think about which basic automation tactic to use, or do some processing
      of hypothesis or the goal itself.
    2. This enables to alleviate the code from trivial but often a tedious proofs,
      making proof clear and easier to maintain
    3. It is actually a reasonable automation tactic:
      - it does enough: it can solve most trivial goals, and when it fails it is
        usually because there is actually some reasoning left to do
      - it is not do too much: its behavior is basically predictable,
        it is usually clear why it works or not
      - it is not too costly: it takes a reasonable amount of time compared to more
        complex solver like [congruence] making it possible to use systematically
        in developments, e.g. as done in [MathComp] using a variant named [done]

    The tactic [easy] also comes as a tactic combinator [Ltac now tac := tac ; easy]
    that runs a tactic [tac] before trying to solve the goal with [easy].
    It allows very compact proof, only showing interesting logical step as shown below:
*)

Goal forall A (l : list A), length l = 0 <-> l = [].
  Proof.
    intros A' l. split.
    - now destruct l.
    - intros H. now rewrite H.
  Qed.

(** Moreover, this is very useful to maintain proof.
    Indeed, as [easy] needs to solve the goal to succeed, if a change now
    leaves a goal unsolved then [now tac] will fails, making it easy to spot.
*)


(** ** 2. What [easy] does

    [Easy] is basically composed of two logical block.
    First, a tactic [do_atom] that tries to solve the goal with basic automation tactics:
*)

Ltac do_atom := solve [ trivial with eq_true | reflexivity | symmetry; trivial | contradiction ].

(** The different tactic serves different purposes:
    1. [trivial] runs a very limited proof search, a version of [auto] that
        only uses hints with cost 0. In particular, while it does it runs
        assumption as usual, it does not apply function in the context:
*)

Goal forall (P : Prop) (p : P), P.
  intros. trivial.
Qed.

Goal forall (P Q R : Prop) (f : P -> Q) (f : Q -> R) (p : P), R.
  intros. Fail progress trivial.
Abort.

(** 2. [reflexivity] checks if the goal is of the form [R x x] where [R] is known
       reflexive relation, e.g. [x = x] or [P <-> P].
    3. [symmetry ; trivial] reverses the equality before running the proof search.
       It can be useful as [symmetry] can not be added directly to the proof search
       as a hint of cost 0 as otherwise it could create a loop.
    4. [contradiction] checks if there is a pair [P,~P] in the context, [x : X]
       where [X] is an empty type like [False], or [~X] where [X] is a unit type
       like [True]

    Second, a tactic that process hypothesis by recursively simplifying
    conjunction checking for inconsistencies. Given an hypothesis [H]:
    - If [H] is a conjunction [H1 /\ H2]:
      1. it checks if [H] proves the goal with [try exact H]
      2. if not, it splits the hypothesis, and recursively simplify [H1] and [H2]
    - If [H] is not a conjunction, it is checks for inconsistent by trying to
      solve the goal with [inversion H]

    The tactic [easy] then recursively:
    1. Tries to solve trivial goals using [do_atom]
    2. If the goal is not trivial, it process the hypothesis [H : _ |- _ ]
       in the context and tries to solve the goal with [do_atom]
    3. Introduce the head variable [_ |- forall (H : _), _], process it,
       and tries to solve the new goal with [do_atom]
    4. If the goal has not been solved yet and is a conjunction [_ |- X1 /\ X2 ],
       it splits the goal and recursively try to solve [X1] and [X2] starting at 3.

    ** Adapting Easy

    As the tactic [easy] is defined in [Ltac], it can at any point be redefined
    to be adapted to your project using the command [Ltac easy ::= tac].
    Doing so will also change [easy] in any other [Ltac] tactic using it in its
    definition.
    In particular, it also changes the terminator [now], enabling to write
    developments as usual but with an adapted tactic.

    For instance, we can set [easy] to [fail] to make it the trivial terminator:
*)

Ltac easy ::= fail "the tactic failed to solve the goal".

Goal forall b : (False), 0 = 1.
  Fail now intro b. intros b. now destruct b.
Qed.

(** However, if you modify [easy] be careful not to loose its terminating behavior.
*)


