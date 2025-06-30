(** * Tutorial: Intro Patterns

  *** Main contributors

    - Thomas Lamiaux, Pierre Rousselin

  *** Summary

  In this tutorial, we discuss intro patterns that enable us to introduce
  hypotheses and transform them at the same time, e.g. by pattern-matching
  or rewriting them. This enables us to factorize and to write more direct code.

  *** Table of content

      - 1. Introducing Variables
      - 2. Destructing Variables
      - 3. Rewriting and Injection
      - 4. Simplifying Equalities
      - 5. Applying Lemmas
      - 6. Intro patterns everywhere

  *** Prerequisites

    Needed:
    - No Prerequisites

    Not Needed:
    - No Prerequisites

    Installation:
  - Available by default with Coq/Rocq

*)

From Coq Require Import List.
Import ListNotations.


(** ** 1. Introducing Variables

    The basic tactic to introduce variables is [intros]. Its most basic form
    [intros x y ... z] will introduce as many variables and hypotheses as
    mentioned with the names specified [x], [y], ..., [z], and fails if one of
    the names is already used, or if there are no more variables or hypotheses
    to introduce.
*)

Goal forall n m, n < m -> n <= m.
Proof.
  intros n m H.
Abort.

Goal forall n m, n < m -> n <= m.
Proof.
  Fail intros n n H.
Abort.

(** It can happen that we have a hypothesis to introduce that is not useful
    to our proof. In this case, rather than introducing it we would rather like
    to directly forget it. This is possible using the wildcard pattern [_], that
    will introduce and forget a variable that does not appear in the conclusion.
*)

Goal forall n m, n = 0 -> n < m -> n <= m.
Proof.
  intros n m _ H.
Abort.

Goal forall n m, n < m -> n <= m.
Proof.
  Fail intros _ m H.
Abort.

(** In some cases, we do not wish to choose a name and would rather have Coq
    choose a name for us. This is possible with the [?] pattern.
*)

Goal forall n m, n < m -> n <= m.
Proof.
  intros n m ?.
Abort.

(** However, be careful that referring explicitly to auto-generated names in a
    proof is bad practice as subsequent modifications of the file could change the
    generated names, and hence break the proof. This can happen very fast.
    Auto-generated names should hence only be used in combination with tactics
    like [assumption] that do not rely on names.

    Similarly to [?], it happens that we want to introduce all the variables
    automatically and without naming them. This is possible by simply writing
    [intros] or as an alias [intros **].
*)

Goal forall n m, n < m -> n <= m.
Proof.
  intros.
Abort.

Goal forall n m, n < m -> n <= m.
Proof.
  intros **.
Abort.

(** As a variant of [intros], [intros *] will introduce all the hypothesis
    from the goal until it reaches one depending on the ones that it is has introduced,
    or that there is no more hypotheses to introduce.
    In this example, [intros *] will introduce [n] and [m], then stops at [n < m]
    as it depends on [n] and [m] that it has just introduced.
*)

Goal forall n m, n < m -> n <= m.
Proof.
  intros *.
Abort.

(** This is particularly convenient to introduce type variables that other variables
    depend upon, but that we do not want to perform any specific action on but introduction.
 *)

Goal forall P Q, P /\ Q -> Q /\ P.
Proof.
  intros *.
Abort.

(** An important difference between [intros] and [intros x] is that [intros]
    introduce as much variables as possible without simplifying the goal,
    whereas [intros x] will first compute the head normal form before trying to
    introduce a variable. This difference can be intuitively understood
    by considering that [intros x] means there is a variable to introduce,
    and requires to find it.

    For instance, consider the definition that a relation is reflexive.
*)

Definition Reflexive {A} (R : A -> A -> Prop) := forall a, R a a.

(** If we try to prove that logical equivalence is reflexive by using [intros]
    then nothing will happen as [Reflexive] is a constant, and it needs to
    be unfolded for a variable to introduce to appear.
    However, as [intros x] simplifies the goal first, it will succeed and progress:
*)

Goal Reflexive (fun P Q => P <-> Q).
  Fail progress intros.
  intros P.
Abort.



(** ** 2. Destructing Variables

  When proving properties, it is very common to introduce variables only to
  pattern-match on them just after, e.g. to prove properties about an inductive type
  or simplify an inductively defined function:
*)

Goal forall P Q, P /\ Q -> Q /\ P.
  intros P Q H. destruct H as [H1 H2]. split.
  + assumption.
  + assumption.
Qed.

Goal forall P Q, P \/ Q -> Q \/ P.
Proof.
  intros P Q H. destruct H as [H1 | H2].
  + right. assumption.
  + left. assumption.
Qed.

(** To shorten the code, it is possible to do both at the same time using the
    intro pattern [[ x ... y | ... | z ... w ]]. It enables to give a
    name to each argument of each constructor, separating them by [|].
    If neither branches nor names are specified, Coq will just use auto-generated names.
*)

Goal forall P Q, P /\ Q -> Q /\ P.
  intros P Q [p q]. split.
  + assumption.
  + assumption.
Qed.

Goal forall P Q, P \/ Q -> Q \/ P.
Proof.
  intros P Q [p | q].
  + right. assumption.
  + left. assumption.
Qed.

(** As a side remark, the fact that intro patterns have the same syntax that
    what is after [as] in [destruct ... as] is no accident, since the [as]
    keyword in a tactic is followed by ... an intro pattern.
*)

Goal forall P Q, P \/ Q -> Q \/ P.
Proof.
  intros P Q [].
  + right. assumption.
  + left. assumption.
Qed.

(** Note that destructing over [False] expects neither branches nor names as [False]
    has no constructors, and that it solves the goal automatically:
*)

Goal forall P, False -> P.
Proof.
  intros P [].
Qed.

(** Using intro patterns is not at all restricted to logical formulas.
    Consider Peano's natural numbers (the type [nat] here).
*)

Print nat.

(** It has two constructors, one called [O : nat] without argument for the
    number zero, and the successor function [S : nat -> nat], basically [1 + _].
    This says that any number of type [nat] is either 0 or the successor of
    another number of type [nat]. This can be used to reason by case analysis on
    (the nullity of) a natural number.
*)

Goal forall (n : nat), n = 0 \/ (exists (m : nat), n = 1 + m).
Proof.
  (* two cases, the first one is empty because [O] has no argument. *)
  intros n. destruct n as [| n'].
  - left. reflexivity.
  - right. exists n'. reflexivity.
Qed.

(** Again, we can [intros] and [destruct] our [n] variable in one step. *)

Goal forall (n : nat), n = 0 \/ (exists (m : nat), n = 1 + m).
Proof.
  intros [| n']. (* two cases, the first one is empty because [O] has no argument. *)
  - left. reflexivity.
  - right. exists n'. reflexivity.
Qed.

(** It is further possible to nest the intro-patterns when inductive types are
    nested into each other:
*)

Goal forall P Q R, (P \/ Q) /\ R -> P /\ R \/ Q /\ R.
  intros P Q R [[p | q] r].
  + left. split; assumption.
  + right. split; assumption.
Qed.

Goal forall P Q R, P /\ (Q /\ R) -> R /\ (Q /\ P).
  intros P Q R [p [q r]].
Abort.

(** Actually, the latter pattern is common enough that there is a specific intro-pattern for it.
    When the goal is of the form [X Op1 (Y ... Opk W)] where all the binary operations
    have one constructor with two arguments like [/\], then it is possible to
    introduce the variables with [intros (p & q & r & h)] rather than by having to
    destruct recursively with [intros [p [q [r h]]] ].
*)

Goal forall P Q R H, P /\ (Q /\ (R /\ H)) -> H /\ (R /\ (Q /\ P)).
Proof.
  intros * (p & q & r & h).
Abort.

(** A particularly useful case is to introduce existentially quantified hypotheses.
*)

Goal forall P Q (f : forall x y, P x y -> Q x y),
     (exists (x y: nat), P x y) -> (exists (x y : nat), Q x y).
Proof.
  intros P Q f (x & y & Pxy).
  exists x, y. apply f. assumption.
Qed.

(** ** 3. Rewriting Lemmas *)

(** It is also very common to introduce an equality that we only wish to use once as a rewrite rule on the goal:
*)

Goal forall n m, n = 0 -> n + m = m.
Proof.
  intros n m H. rewrite H. cbn. reflexivity.
Qed.

(** It is possible to do both at the time using the intro patterns [->] and
    [<-] that will introduce [H], rewrite it in the goal and context and then clear it.
    It has the advantage to be much more concise, and save us from introducing
    a name for [n = 0] that we fundamentally do not really care about:
*)

Goal forall n m, n = 0 -> n + m = m.
Proof.
  intros n m ->. cbn. reflexivity.
Qed.

Goal forall n m, 0 = n -> n + m = m.
Proof.
  intros n m <-. cbn. reflexivity.
Qed.

Goal forall n m p, n + p = m -> n = 0 -> p = m.
Proof.
  intros n m p H ->. cbn in *. apply H.
Qed.

(** For a more concrete example, consider proving that if a list has one element
    and another one is empty, then the concatenation of the two lists has one element.
    The usual proof would require us to introduce the hypothesis and decompose it
    into pieces before being able to rewrite and simplify the goal:
*)

Goal forall {A} (l1 l2 : list A) (a : A),
    l1 = [] /\ l2 = [a] \/ l1 = [a] /\ l2 = [] -> l1 ++ l2 = [a].
Proof.
  intros A l1 l2 a.
  intros H. destruct H as [H | H].
  - destruct H as [H1 H2]. rewrite H1, H2. reflexivity.
  - destruct H as [H1 H2]. rewrite H1, H2. reflexivity.
Qed.

(** Using intro patterns to do the pattern-matching and the rewriting, we can get
    a very intuitive and compact proof without having to introduce any fresh names: *)

Goal forall {A} (l1 l2 : list A) (a : A),
    l1 = [] /\ l2 = [a] \/ l1 = [a] /\ l2 = [] -> l1 ++ l2 = [a].
Proof.
  intros A l1 l2 a [[-> ->] | [-> ->]].
  - reflexivity.
  - reflexivity.
Qed.


(** ** 4. Simplifying Equalities

  Rewriting automatically equalities is practical but sometimes we first need to
  simplify them with [injection] before being able to rewrite with them.
  For instance in the example below, we have an equality [S n = 1] but
  as it is [n] that appears in the conclusion, we first need to simplify the equation
  with [injection] to [n = 0] before being able to rewrite it.
*)

Goal forall n m, S n = 1 -> n + m = m.
Proof.
  intros n m H. injection H. intros H'. rewrite H'. cbn. reflexivity.
Qed.

(** To do this automatically, there is a dedicated intro pattern [ [=] ]
    that will introduce the equalities obtained after simplification by [injection].
*)

Goal forall n m, S n = S 0 -> n + m = m.
Proof.
  intros n m [= H]. rewrite H. cbn. reflexivity.
Qed.

(** It is then possible to combine this with the intro pattern for rewriting to
    directly simplify the goal, giving us a particularly simple proof.
*)

Goal forall n m, S n = S 0 -> n + m = m.
Proof.
  intros n m [= ->]. cbn. reflexivity.
Qed.

(** Another particularly useful way of simplifying an equality is to deduce that the
    goal is true from an absurd equation like [S n = 0].
    This is usually done by introducing variables then using [discriminate],
    but can also be automatically done thanks to the intro pattern [=]:
*)

Goal forall n, S n = 0 -> False.
Proof.
  intros n [=].
Qed.

(** ** 5. Applying Lemmas

  A situation that often arises when proving properties is having a hypothesis
  that we first need to transform before being able to use it.

  For instance, consider the following example where we know that [length l1 = 0].
  To conclude that [l1 ++ l2 = l2], we must first prove that [l1 = []] by
  applying [length_zero_iff_nil] to [length l1 = 0], and then rewrite it:
*)

Goal forall A (l1 l2 : list A), length l1 = 0 -> l1 ++ l2 = l2.
Proof.
  intros A l1 l2 H. apply length_zero_iff_nil in H. rewrite H. cbn. reflexivity.
Qed.

(** To help us do this, the [%] intro pattern [H%impl] introduces the
    hypothesis [H] and applies the implication [impl] in it. We can hence write
    [intros H%length_zero_iff_nil] rather than [intros H. apply length_zero_iff_nil in H].
*)

Goal forall A (l1 l2 : list A), length l1 = 0 -> l1 ++ l2 = l2.
Proof.
  intros A l1 l2 H%length_zero_iff_nil. rewrite H. cbn. reflexivity.
Qed.

(** We can then further combine this with rewrite patterns to simplify the proof:
*)

Goal forall A (l1 l2 : list A), length l1 = 0 -> l1 ++ l2 = l2.
Proof.
  intros A l1 l2 ->%length_zero_iff_nil. cbn. reflexivity.
Qed.

(** For a more involved example, consider the converse of the last example of section 3:
    if the concatenation of two lists has one element, then one list has one
    element and the other one is empty.

    After pattern matching on [l1], we have an equality [a1::l1++l2 = [a]]. We
    must simplify it to [a1 = a] and [l1 ++ l2 = []] with [injection], then to
    [l1 = []] and [l2 = []] with [app_eq_nil], before being able to rewrite.
    This creates a lot of overhead as introduction and operations like
    destruction, simplification and rewriting have to be done separately.
    Furthermore, at every step we have to introduce fresh names that do not really
    matter in the end.
*)

Goal forall {A} (l1 l2 : list A) (a : A),
    l1 ++ l2 = [a] -> l1 = [] /\ l2 = [a] \/ l1 = [a] /\ l2 = [].
Proof.
  intros A l1 l2 a. destruct l1; cbn.
  - intros H. rewrite H. left. split; reflexivity.
  - intros H. injection H. intros H1 H2. rewrite H2. apply app_eq_nil in H1.
    destruct H1 as [H3 H4]. rewrite H3, H4. right. split; reflexivity.
Qed.

(** Using intro patterns we can significantly shorten this proof and make it
    more intuitive, getting rid of tedious manipulations of hypotheses.

    We can use the intro pattern [[=]] to simplify the equality [a1::l1++l2 = [a]]
    to [a1 = a] and [l1 ++ l2 = []]. We can then rewrite the first equality
    with [->], and simplify the second equality to [l1 = [] /\ l2 = []] thanks
    to [%app_eq_nil]. Finally, we can rewrite both equalities using [->], giving
    us the intro pattern [intros [= -> [-> ->]%app_eq_nil]].
    This yields a much shorter proof without a bunch of fresh names.
*)

Goal forall {A} (l1 l2 : list A) (a : A),
    l1 ++ l2 = [a] -> l1 = [] /\ l2 = [a] \/ l1 = [a] /\ l2 = [].
Proof.
  intros A l1 l2 a. destruct l1; cbn.
  - intros ->. left. split; reflexivity.
  - intros [= -> [-> ->]%app_eq_nil]. right. split; reflexivity.
Qed.

(** ** 6. Intro patterns everywhere *)

(** We mentioned before the fact that the tactic [destruct ... as ...] expects
    an intro pattern after [as].

    In fact, many tactics can have an [as ...] part, with an intro pattern.

    Let's give examples. *)

(** We concentrate on [apply ... in ...]. In general, using this tactic can
    result in a weaker proof state, which may or may not be an issue. *)

Goal forall (P Q R : Prop), (P -> Q) -> P -> (P -> R) -> Q /\ R.
Proof.
  intros P Q R H1 H2 H3.
  (* Now I'm tired and I want to deduce that [Q] holds. *)
  apply H1 in H2.
  (* Ouch, no more way to prove that [P] holds! *)
Abort.

Goal forall (P Q R : Prop), (P -> Q) -> P -> (P -> R) -> Q /\ R.
Proof.
  intros P Q R H1 H2 H3.
  (* Now I'm less tired and I give a new name to what I deduce from [H1] and
     [H2]. *)
  apply H1 in H2 as HQ.
  (* This is fun, I can do this with a proof of [R], too. *)
  apply H3 in H2 as HR.
  split.
  - assumption.
  - assumption.
Qed.

(** In many cases, applying an implication in an hypothesis will give something
    which:
    - can (and should) be [destruct]ed with [[...]] or
    - is an equality to use with [rewrite] with [->] or [<-] or
    - can be simplified ([injection]), or is directly contradictory
      [discriminate] (with [[= ...]]) or
    - can be served as a condition to another implication with [%]
    In that case, we're free to use everything we already learned after [as]. *)

Goal forall (P Q R : Prop) (n : nat), (Q -> S n = S 21) -> (P -> Q /\ R) -> P ->
  (n + n = 42).
Proof.
  intros P Q R n H1 H2 H3.
  apply H2 in H3 as [HQ _]. (* "and" intro pattern, drop a useless part *)
  apply H1 in HQ as [= ->]. (* injection, then rewrite *)
  reflexivity.
Qed.

(** We can go crazier: *)
Goal forall (P Q R : Prop) (n : nat), (Q -> S n = S 21) -> (P -> Q /\ R) -> P ->
  (n + n = 42).
Proof.
  intros P Q R n H1 H2 H3.
  apply H2 in H3 as [[= ->]%H1 _].
  reflexivity.
Qed.

(** Who needs [apply]? *)
Goal forall (P Q R : Prop) (n : nat), (Q -> S n = S 21) -> (P -> Q /\ R) -> P ->
  (n + n = 42).
Proof. intros P Q R n H1 H2 [[= ->]%H1 _]%H2. reflexivity. Qed.

(** Other useful and frequently used tactics which can be used with
    [as intro_pattern] include:
    - [destruct]
    - [pose proof]
    - [specialize]
    - [assert] and [enough]
    - [inversion] (restricted to "and" and "or" intro patterns)
    - [injection]
*)

Goal forall (n m : nat), n * 2 + n * m = 0 -> n + m = m.
Proof.
  intros n m H.
  enough (n = 0) as ->. {
    reflexivity.
  }
  rewrite <-PeanoNat.Nat.mul_add_distr_l in H.
  pose proof PeanoNat.Nat.mul_eq_0 as mul0.
  (* specialize and discard useless right to left implication: *)
  specialize (mul0 n (2 + m)) as [H' _].
  (* apply H' in H and reason by case
     - in the first one, change 0 with n in the goal
     - in the second one, 2 + m = 0 can be reduced to (S (S m) = 0) which is
       discriminable.
  *)
  apply H' in H as [<- | [=]].
  reflexivity.
Qed.
