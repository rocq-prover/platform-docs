(** * Tutorial: Chaining Tactics

  *** Main contributors

    - Thomas Lamiaux

  *** Summary

  In this tutorial, we explain how to chain tactics together to write more concise code.

  *** Table of content

      - 1. Introduction to Chaining
      - 2. Chaining Selectively on Subgoals
        - 2.1 Basics
        - 2.2 Ignoring Subgoals when Chaining
        - 2.3 Chaining on a Range of Sugoals
      - 3. Chaining is actually backtracking
      - 4. Repeating Tactics and Chaining

  *** Prerequisites

    Needed:
    - No Prerequisites

    Not Needed:
    - No Prerequisites

    Installation:
  - Available by default with Rocq

*)




(** ** 1. Introduction to Chaining

*)

Section Chaining.
  Context (A B C D E F : Type).

  Set Printing Parentheses.

(** In Rocq, we prove theorems interactively, applying at each step a tactic
    that transform the goal, and basically corresponds to applying a logical resonning.
    Yet, in practice, it often happens that some of the primitive tactics are too low-level,
    and that a higher-level resoning step we would like to do gets decomposed into
    a sequence of tactics, and hence of interactive steps.
    This is not very practical, as it hinders understanding when stepping through a proof.
    It introduces extra interactive steps that we do not care about and can be tedious to run,
    but also makes the logical structure of the proof harder to recognize and understand.

    For instance, consider the second subgoal of the proof below.
    Knowing [a : A] and [b : B], we have to prove [(A * B) + (A * C) + (A * D)],
    and hence would like to bring ourselves back to proving [A * B].
    While this corresponds to one simple logical step, it actually gets decomposed
    into two tactics applied in a row [left. left.].
*)

  Goal A * (B + C + D) -> A * B + A * C + A * D.
    intros x. destruct x as [a x]. destruct x as [[b | c] | d].
    - left. left. constructor.
      -- assumption.
      -- assumption.
    - left. right. constructor.
      -- assumption.
      -- assumption.
    - right. constructor.
      -- assumption.
      -- assumption.
  Qed.

(** To recover the correspondence between the interactive steps and the logical steps
    we have in mind, we would like to be able to chain tactics, so that in the example
    [left] and [right] are excuted together, one after the other.
    This is possible using the notation [tac1 ; tac2] that is going to execute
    the tactic [tac1], and then [tac2] on all the subgoals created by [tac1].

    In our case, it enables us to write [left; left.] rather than [left. left.]
    to get one logical step:
*)

  Goal A * (B + C + D) -> A * B + A * C + A * D.
    intros x. destruct x as [a x]. destruct x as [[b | c] | d].
    - left; left. constructor.
      -- assumption.
      -- assumption.
    - left; right. constructor.
      -- assumption.
      -- assumption.
    - right. constructor.
      -- assumption.
      -- assumption.
  Qed.

(** The real strength of chaining tactics appears when different subgoals are
    created by a tactic, e.g [tac1], that requires the same kind of proofs, e.g. [tac2].
    Indeed, in such cases, by chaining tactics [tac1] to [tac2], we can apply
    [tac2] on all subgoals created by [tac1] at once, and do not have
    to repeat [tac2] for each subgoal.

    In general, this enables to greatly factorise redundant code, while flattening
    the code that is needing less sub-proofs / bullets.

    Typically, in the example above, in all the cases created by [constructor],
    we want to apply [assumption] to conclude the proof.
    We can hence share the code by writing [constructor; assumption] rather
    than dealing with each subgoal independently, and in total to remove 6 subproofs.
    This greatly simplifies the proof structure, while better reflecting the logical structure.
*)

  Goal A * (B + C + D) -> A * B + A * C + A * D.
    intros x. destruct x as [a x]. destruct x as [[b | c] | d].
    - left; left. constructor; assumption.
    - left; right. constructor; assumption.
    - right. constructor; assumption.
  Qed.


(** ** 2 Chaining Selectively on Subgoals

    *** 2.1 Basics

    Chaining tactics with [tac1 ; tac2] applies the tactic [tac2] to all the subgoals created by [tac1].
    Yet, it is not always subtle enough as different subgoals can require
    slightly different kind of reasoning.

    For instance, consider the example below where we need to apply different functions
    to each subgoal, namely applying [fAC] in one case and [fBD] in the other case:
*)

  Goal (A -> C) -> (B -> D) -> A * B -> C * D.
    intros fAC fBD p. destruct p as [a b].
    constructor.
    - apply fAC. assumption.
    - apply fBD. assumption.
  Qed.

(** Yet, we would still like to be able to chain tactics together to factorise code and make it clear.
    It is possible by using the notation [ tac; [tac1 | ... | tacn] ] that takes exactly
    a tactic per subgoal created by [tac], and apply [taci] on the i-th subgoal

    This enables us to chain [constructor] with the [apply] by writing
   [ constructor; [apply fAC | apply fBD] ].
*)

  Goal (A -> C) -> (B -> D) -> A * B -> C * D.
    intros fAC fBD p. destruct p as [a b].
    constructor; [apply fAC | apply fBD].
    - assumption.
    - assumption.
  Qed.

(** This is particularly practical when the subgoals created require
    a slightly different logical step, before resuming the same proof script.
    In which case, we can use goal selection to do a differentiated reasoning
    step before resuming regular chaining.

    For instance, in the proof above, in both case, we conclude the proof
    with [assumption] after applying [fAC] or [fBC].
    We can hence further chain [ [apply fAC | apply fBD] ] with [assumption]
    to provide a significantly shorter proof:
*)

  Goal (A -> C) -> (B -> D) -> A * B  -> C * D.
    intros fAC fBD p. destruct p as [a b].
    constructor; [apply fAC | apply fBD] ; assumption.
  Qed.


(** *** 2.2 Ignoring Subgoals when Chaining

    The construction [tac ; [tac1 | ... | tacn] ] requires a tactic per subgoal.
    Yet, in some cases, before continuing the common proof, an action is needed
    for only one subgoal.

    For instance, consider a ternary version of the example above.
    Using [constructor] creates a subgoal where we need to use [constructor]
    again, before continuing the same usual proof.
    We hence, would like to apply [constructor] once more, but only on the first branch.
*)

  Goal (A -> D) -> (B -> E) -> (C -> F) -> A * B * C -> D * E * F.
    intros fAD fBE fCF p. destruct p as [[a b] c].
    constructor.
    - constructor.
      -- apply fAD; assumption.
      -- apply fBE; assumption.
    - apply fCF; assumption.
  Qed.

(** This is possible by either:
    - 1. leaving the tactic spot empty
    - 2. using the [idtac] tactic that does nothing

    This enables to flatten the code removing the number of nested subgoals to prove,
    while better reflecting the natural structure of the proof:
*)

  Goal (A -> D) -> (B -> E) -> (C -> F) -> A * B * C -> D * E * F.
    intros fAD fBE fCF p. destruct p as [[a b] c].
    constructor; [constructor|].
    - apply fAD; assumption.
    - apply fBE; assumption.
    - apply fCF; assumption.
  Qed.

  Goal (A -> D) -> (B -> E) -> (C -> F) -> A * B * C -> D * E * F.
    intros fAD fBE fCF p. destruct p as [[a b] c].
    constructor; [constructor| idtac].
    - apply fAD; assumption.
    - apply fBE; assumption.
    - apply fCF; assumption.
  Qed.

(** If wished, it is then possible to further factorise the structure by
    chaining the [apply] and [assumption] as before.
*)

  Goal (A -> D) -> (B -> E) -> (C -> F) -> A * B * C -> D * E * F.
    intros fAD fBE fCF p. destruct p as [[a b] c].
    constructor; [constructor |]; [apply fAD | apply fBE | apply fCF]; assumption.
  Qed.

(** However, as you can see it does not necessarily make the proof clearer.
    Chaining is great but be careful not to overuse as it can create long and
    unreadable proof, that no longer reflect logical steps.

    This construction is also particularly practical to get rid of trivial subgoals
    that are generated by a tactic. For instance, consider, the proof below where
    a trivial subgoal is generated by [constructor]:
*)

  Goal (B -> D) -> (C -> D ) -> A * (B + C) -> A * D.
    intros fBD fCD p. destruct p as [a x].
    constructor.
    - assumption.
    - destruct x; [apply fBD | apply fCD] ; assumption.
  Qed.

(** Chaining with [ [assumption |] ] enables to get rid of the trivial goal,
    making the proof flatter and letting us focus on the main goal:
*)

  Goal (B -> D) -> (C -> D ) -> A * (B + C) -> A * D.
    intros fBD fCD p. destruct p as [a x].
    constructor; [assumption |].
    destruct x; [apply fBD | apply fCD] ; assumption.
  Qed.

(** Note, that it is also possible with the notation [only n: tac] that applies a
    tactic only to the n-th goal.
 *)

  Goal (B -> D) -> (C -> D ) -> A * (B + C) -> A * D.
    intros fBD fCD p. destruct p as [a x].
    constructor; only 1: assumption.
    destruct x; [apply fBD | apply fCD] ; assumption.
  Qed.


(** *** 2.3 Chaining on a Range of Sugoals

    It often happens that we have several subgoals, for which we want to apply
    the same tactic, or do nothing.

    For instance, in the following context, applying [up] to prove [forall a : A, D]
    creates a bunch of goals that all get solved by [assumption] but one:
*)

  Section Range.
    Context (up : (A -> D) -> (B -> D) -> (C -> D) -> A + B + C -> D).
    Context (fA : A -> D).
    Context (fB : B -> D).
    Context (fC : C -> D).

    Goal forall (a : A), D.
      intros a. apply up.
      - assumption.
      - assumption.
      - assumption.
      - left; left. assumption.
    Qed.

(** Consequently, we would like to apply [assumption] on the first three subgoals to
    get rid of the trivial goals before tackling the last one.

    There are basically three facilities to do that, we can:
    - 1. Use the notation [only m-n,..., p-q: tac], that applies [tac] to the ranges of
      subgoals [n-m], ..., and [p-q]
    - 2. Use the [..] notation to apply a tactic to all the subgoal until the
         next one specified like in [ [tac1 | tac2 .. | tack | tac n ]].
    - 3. Use the combinator [try tac] that tries to apply [tac] to all the
         subgoals, and it succeeds if no progress is possible
*)

    Goal forall (a : A), D.
      intros a. apply up; only 1-3:assumption.
      left; left; assumption.
    Qed.

    Goal forall (a : A), D.
      intros a. apply up; [ assumption .. | ].
      left; left. assumption.
    Qed.

    Goal forall (a : A), D.
      intros a. apply up; try assumption.
      left; left. assumption.
    Qed.

    (* try always succeeds *)
    Goal forall (a : A), D.
      intros a. apply up; try fail.
    Abort.

(** Note that in this very particular case, we could have used first [left; left]
    on the last goal then applied [assumption] everywhere, but it is not a good
    idea in the facing case, we can hardly predict how difficult will be the last goal.
*)

  End Range.


(** ** 3 Chaining is actually backtracking

    A subtility with chaining tactics is that [tac1 ; tac2] does not only
    chain tactics together, applying [tac2] on the subgoals created by [tac1],
    but also does backtracking.

    If the tactic [tac1] makes choice out of several possible ones, e.g. which
    constructor to apply, and [tac2] fails with this choice, then [tac1; tac2]
    will backtrack to [tac1], make the next possible choice and try [tac2] again.
    This until a choice makes [tac1 ; tac2] succeed, or that all the possible
    choice for [tac1] are exhausted, in which case [tac1 ; tac2] fails.

    This is the case of the tactic [constructor] that tries to apply the first
    constructor of an inductive type by default, and will backtrack to try
    the second constructor and so on if the rest of the proof failed.

    This enables to write more concise proofs as we can write the same script
    whatever the constructor we need to apply to keep going and complete the proof.

    Consider, the following proof where we have to choose between proving the
    left side [A * B] or the right side [A * C] depending on which subgoals we
    are trying to prove and our hypothesis:
*)

  Goal A * (B + C + D) -> A * B + A * C + A * D.
    intros x. destruct x as [a x]. destruct x as [[b | c] | d].
    - left; left. constructor; assumption.
    - left; right. constructor; assumption.
    - right. constructor; assumption.
  Qed.

(** Using [constructor], we can replace [left] and [right] to get the same
    proof script for the first and second goal, as:
    - for the first goal, it will try [left], continue with [assumption] and solve the goal
    - for the second goal, it will try [left], continue with [assumption] and fail,
      hence backtrack and try [right], continue the proof and succded
*)

  Goal A * (B + C + D) -> A * B + A * C + A * D.
    intros x. destruct x as [a x]. destruct x as [[b | c] | d].
    - left; constructor; constructor; assumption.
    - left; constructor; constructor; assumption.
    - right. constructor; assumption.
  Qed.

(** It can be a bit confusing at first, but once we got used to it, it is very
    practical to write one proof script to deal with a bunch of barely different
    subgoals.

    For instance, we can then further simplify the proof by factorising the [left] and [right]
    of the first and third subgoal. Then by using [only 1-2:] for the extra [constructor],
    of the first two subgoals, we can get one single proof script to solve all the goals:
*)

  Goal A * (B + C + D) -> A * B + A * C + A * D.
    intros x. destruct x as [a x]. destruct x as [[b | c] | d].
    all: constructor; only 1-2: constructor; constructor; assumption.
  Qed.

(** Using the backtracking ability of [;] to make the right choice out of
    several possible choices is a simple but very powerful method that enables us
    to write short but versatile proof scripts.
*)



(** ** 4. Repeating Tactics

    In the previous section, we have explained how to chain tactics linearly so
    that they execute one after the other, on respectively created subgoals.
    While this is already very practical, in some cases, we need a bit more
    freedom like to be able to repeat tactics, or to try a set of tactics.
    This is what we discuss in this section.

    Consider the following example of section 1, that has ~25 interactive steps,
    6 sub-proofs and is 10 lines long, even though it is a fairly simple proof.
*)

  Goal A * (B + C + D) -> A * B + A * C + A * D.
    intros x. destruct x as [a x]. destruct x as [[b | c] | d].
    - left. left. constructor.
      -- assumption.
      -- assumption.
    - left. right. constructor.
      -- assumption.
      -- assumption.
    - right. constructor.
      -- assumption.
      -- assumption.
  Qed.

(** Chaining tactics linearly, we have managed to bring down the proofs to
    only three interactive steps corresponding to the three logical steps of
    the proof, and to only two lines.
*)

  Goal A * (B + C + D) -> A * B + A * C + A * D.
    intros x. destruct x as [a x]. destruct x as [[b | c] | d].
    all: constructor; only 1-2: constructor; constructor; assumption.
  Qed.

(** That is already nice, but the proof is still convoluted.
    Not only do we have to repeat [constructor] three times, but we have to
    think by ourselves when writing the proof that for the third case we only need
    [constructor] once and not twice, and hence write [only 1-2: constructor].


    This, even though, the proof is conceptually simple: depending on our case
    select the appropriate subtype to prove, e.g. [A * C], and prove it
    with [constructor; assumption].

    This is particular annoying as it does not scale very well.
    Consider, this small variant with only two more types to distribute on.
    The proof and its overhead then gets much greater, even though it is
    conceptually as simple as before.
*)

  Goal A * (B + C + D + E + F) -> A * B + A * C + A * D + A * E + A * F.
    intros x. destruct x as [a x]. destruct x as [[[[b | c] | d] | e] | f].
    all: constructor;
         only 1-5: constructor;
         only 1-4: constructor;
         only 1-3: constructor;
         only 1-2: constructor;
         assumption.
  Qed.

(** Instead, we would like to be able to apply [constructor] as much as needed
    using the backtracking to choose the good subtype to prove; then concludes
    with [constructor; assumption].

    This is possible with the [repeat tac] combinator, that given a tactic
    will apply it repeatedly until it can no longer be applied, or fails if it
    can not be applied at all.

    This enables us to refactor the proof by simply writing [repeat constructor; assumption],
    getting a proof that now fully correspond to the logical steps we wanted to take.
    It further scales much better, as it works exactly the same for the variant
    with two more types.
*)

  Goal A * (B + C + D) -> A * B + A * C + A * D.
    intros x. destruct x as [a x]. destruct x as [[b | c] | d].
    all: repeat constructor; assumption.
  Qed.

  Goal A * (B + C + D + E + F) -> A * B + A * C + A * D + A * E + A * F.
    intros x. destruct x as [a x]. destruct x as [[[[b | c] | d] | e] | f].
    all: repeat constructor; assumption.
  Qed.

(** However, [repeat] can be a bit subtle, so be careful not to fall into this
    two pitfalls:
    - 1. [repeat] will stop if it succeeds, but it may not be what you expect
      especially when backtracking is involved

      Consider the example above. [repeat constructor; assumption] manages to
      solve the subgoals because it tries to apply [constructor] as much as it
      can, then to solve the subgoals created by [assumption] and if it
      fails backtracks to make other choices.
      If you stop linking them, then [repeat constructor] will just apply
      contructor as much as it can; getting us to prove [A * B] then [A] and [B]
      in each case, getting us stuck.
      In other words [repeat constructor; assumption] is not the same as
      [repeat constructor. all: assumption]:
*)

  Goal A * (B + C + D + E + F) -> A * B + A * C + A * D + A * E + A * F.
    intros x. destruct x as [a x]. destruct x as [[[[b | c] | d] | e] | f].
    all: repeat constructor. Fail all: assumption.
    (* First case: proving A and B *)
    - assumption.
    - assumption.
    (* Second case: proving A and B rather than A and C *)
    - assumption.
    - Fail assumption.
  Abort.

(** - 2. [repeat] will apply a tactic as much as possible, it can be more than what you expect

      Consider proving the same goal as before but with [A] instantiated to [nat].
      You would expect that in both cases, [repeat constructor] gets you into proving
      [nat * B] then [nat] and [B] just like explained before.
      However, running it will actually create only two goals [B] and [B]
      The reason is that [constructor] applies to [nat], and solve the goals using [0]
      even though you would wanted to solve it using [n].
 *)

  Goal nat * (B + C + D) -> nat * B + nat * C + nat * D.
    intros x. destruct x as [n x]. destruct x as [b | c].
    all: repeat constructor.
    Show Proof.
  Abort.

(** Such issues can be particularly annoying getting you stuck in an unprovable
    goal, providing the wrong witness or wrongly unifying a metavariable,
    impact the rest of the proof and getting you stuck latter on.
    Once should hence be careful when it comes to using tactics combinator like [repeat].

    The [repeat] combinator also comes as a variant named [do n tac] that enables
    to apply [tac] exactly [n] times, and if it cannot do it exactly [n] times
    fails:
*)

Goal A -> B -> C -> D -> E -> F.
  do 4 intros ?.
Abort.

Goal A -> B -> C -> D -> E -> F.
  Fail do 8 intros ?.
Abort.

End Chaining.
