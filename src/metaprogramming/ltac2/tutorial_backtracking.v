(** * Tutorial Ltac2 : Backtracking

  *** Authors
  - Thomas Lamiaux
  - Josselin Poiret

  *** Summary

  Ltac2 has native support for backtracking, and powerful primitives to
  manipulate it enabling us to write powerful automatisation proof script.
  In this tutorial, we explain how backtracking works in Ltac2, and how to use
  the different primitives to manipulate backtracking by recoding basics tactics
  that were hardcoded in Ltac1.

  *** Table of content

  - 1. Introduction to Backtracking
    - 1.1 The Stream Model
    - 1.2 backtracking and Goal Focusing
  - 2. Using [Control.zero] to Raise Exceptions
  - 3. Using [Control.Plus] to Stack Possibilities
    - 3.1 Reimplementing [+]
  - 4. Using [Control.Case] to Inspect Backtracking
    - 4.1 Reimplementing [||]
    - 4.1 Reimplementing [once]

  *** Prerequisites

  Disclaimer:
    - You can go a **long way** with Ltac2 without ever needing to directly
      manipulate backtracking, outside of predefined functions like
      [constructor], [once] or [match!].
      This tutorial is for users wanting a deeper understanding of how
      backtracking works, and advanced users of Ltac2.

  Needed:
  - Already know the basics of Ltac2.
  - Having used Ltac2 before.

  Installation:
  - Ltac2 and its core-library are available by default with Rocq

*)


(** Let us start by importing Ltac2, and write a small function for
    printing the current goals to check out what is going on.
    Understanding what is going on is not important for the rest of the tutorial.
*)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Printf.
From Ltac2 Require Import Notations.

Ltac2 print_goals0 () :=
  Control.enter (fun () =>
  match! goal with
  [ |- ?t] => printf "the goal is %t" t
  end
  ).

Ltac2 Notation print_goals := print_goals0 ().

Ltac2 only0 (startgoal : int) (endgoal : int option) (tac : unit -> 'a) : 'a :=
  let clamp i :=
    if (Int.lt i 0)
    then Int.add (Int.add i (Control.numgoals ())) 1
    else i
  in
  let endgoal := Option.default startgoal endgoal in
  Control.focus (clamp startgoal) (clamp endgoal) tac.

Ltac2 Notation "only" startgoal(tactic) endgoal(opt(seq("-", tactic))) ":" tac(thunk(tactic)) :=
  only0 startgoal endgoal tac.






(** ** 1. Introducing on Backtracking

  In Rocq, all tactics are potentially backtracking.

  For instance, when chained with another tactic [tac1 ; tac2], [tac1] can
  succeed but can lead to subsequent failure of [tac2], e.g. because [tac1] pick
  the wrong branch of [False \/ True].
  In this case, if [tac2] fails triggering backtracking, it will backtrack to
  [tac1], try its next success if there is one, then try [tac2] again.
  This until either all possibilities have been exhausted or [tac2] succeeds for
  one of the success procuded by [tac1].

  The most well known example is the [constructor] tactic that tries the
  constructors one by one, until one leads to a success or all constructors have
  been tried in which case it fails.
*)

Goal False \/ True.
  constructor; print_goals; exact I.
Qed.

(** In practice, most people needing backtracking only ever need predefined
    function like [constructor], [first], [once], or the different versions of
    match like [lazymatch!] that handle backtracking for us.

    In this tutorial, we go further than this and explain how backtracking works
    in Ltac2, and how it can be manipulated through set of three basic primitives.
*)


(** *** 1.1 The Stream Model

    In Ltac2 backtracking is primitive.

    This means that every Ltac2 term is potentially backtracking, and that there is no
    distinction in the type of a term that can backtrack compared to one that can not.
    For example, both tactics [constructor] and [left] are of type [unit],
    even though the first one can backtrack, but not the second one.

    Unlike typical programming languages, in Ltac2, a term should not be viewed
    as producing a single value, but instead as stream of possible values to be tried.

    The first term gets tried, i.e. the head of the stream, and if this choice
    leads to a subsequent failure and to backtracking, then it tries the second term,
    i.e. the new head of the stream, and so on.
    This goes on until either a value leads to a success, or all possibilities
    have been exhausted in which case it triggers a backtracking error.
    Note that this can last forever as stream are potentially infinite.

    To understand this better, consider using [constructor; exact I] to prove [False \/ True].
    [constructor] can have two successes [left] and [right], are this are the
    two constructors of [\/], and can hence be viewed as the stream [left :: right].
    When chained with [exact I], this will first try [left] as it is the head
    of the stream. This leads to the goal [False] on which [exact I] fails.
    It will hence backtrack and to try the next success [right], which this time
    leads to [True I] on which [I] succeed. Consequently, the whole tactic succeeds.
*)

Goal False \/ True.
  constructor; print_goals; exact I.
Qed.

(** If we try [constructor; assumption] instead, this will try [left] then [right]
    which both lead to goals that can not be solved by [assumption].
    It will hence reach the empty stream and trigger backtracking.
    As they are no previous backtracking point to backtrack to,
    it will just fail here returning the last error message.
*)

Goal False \/ True.
  Fail constructor; print_goals; assumption.
Abort.

(** That terms represent streams is true for every term, not just for terms of type [unit].
    For instance [n : nat], should not be viewed as a single value like [3],
    but instead as a potentially empty or infinite stream of integers like [3;4;3;4;9;...].
*)


(** *** 1.2 Backtracking and Goal Focusing

  In previous examples, we have used our tactics with exactly one focus goal.
  How does backtracking works if more than one goal is focused?

  Do you think it:
  1. Find one unique term in the stream of possibilitities that leads to a success for all the goals,
  2. Or for each goal independently, find one term in the stream that leads to a success.
     Hence, possibly choosing different solutions for each goal.

  To check how it works let us assume the following definition -- that will be
  explained later in this tutorial -- which basically creates the stream [left;right].
*)

Ltac2 Notation left_or_right := Control.plus (fun () => left) (fun _ => right).

(** If it must pick one term to succeed on all goals, [left_or_right; reflexivity]
    should fail to prove [0 = 0 \/ 0 = 1] and [1 = 0 \/ 1 = 1] as:
    - picking [left] for both goals leads to [0 = 0] and [1 = 0], and [reflexivity]
      fails on [1 = 0]
    - picking [right] for both goals leads to [0 = 1] and [1 = 1], and [reflexivity]
      fails on [0 = 1]

    If it must pick on term independently for each goal it should succeed,
    as it can pick [left] for the first goal and [right] for the second leading
    to the goals [0 = 0] and [1 = 1] which both can be solved by [reflexivity].
*)

Goal (0 = 0 \/ 0 = 1) /\ (1 = 0 \/ 1 = 1).
  split.
  Fail all: left_or_right; print_goals; reflexivity.
Abort.

(** As it can be seen above, this fails, consequently, by default backtracking
    must pick one solution for every goal.
    This can be surprising at first, but it actually makes perfect sense.
    If you want one solution per goal, it suffices to focus the goal and to apply
    the tactic one by one using [Control.enter : (unit -> unit) -> unit].
    If you decide to focus several goals and apply a tactic at once,
    it is because you want one solution for all the goals.
*)

Goal (0 = 0 \/ 0 = 1) /\ (1 = 0 \/ 1 = 1).
  split.
  all: Control.enter (fun _ => left_or_right); print_goals; reflexivity.
Qed.

(** In practice, most times, we want an independent choice for each goal.
    Therefore, most basic tactics and tactic cominators like [constructor] or [first] are
    already wrapped in [Control.enter] for us, so we don't have to think about it.

    In the rest of the tutorial, we will recode basic constructor so
    we need to think about it.
 *)



(** Ltac2 offers a complete set of primitive functions to manipulate backtracking:
    - [Control.zero : exn -> 'a]
    - [Control.plus : (unit -> 'a) -> (exn -> 'a) -> 'a]
    - [Control.case : (unit -> 'a) -> ('a * (exn -> 'a)) result]

    We will now see how backtracking and this primitives work by recoding some
    of Ltac2 tactic combinators.
*)


(** 2. Using [Control.zero] to Raise Exceptions

    Suppose we want to re-implement a tactic like [eassumption] that checks if
    the goals corresponds to an hypothesis, possibly unifying evariables.
    Basically, it amounts to matching the goal for an hypothesis [h] that has
    the same type has the goal to prove, and do exact [h].
    If we don't find a suitable assumption, we have to raise an exception.
    `Control.zero` of type [exn -> unit] is the function for the job.
    It will raise the exception given as an argument, and trigger backtracking.

    Here, we raise a generic exception `Tactic_failure` with an optional error
    message of type [message]:
*)

Ltac2 my_eassumption0 () :=
  match! goal with
  | [ h : _ |- _ ] => let h := Control.hyp h in exact $h
  | [ |- _ ] => Control.zero (Tactic_failure (Some (fprintf "No such assumption")))
  end.

Ltac2 Notation my_eassumption := my_eassumption0 ().

Goal (nat -> False -> True \/ False).
  intros ??.
  Fail my_eassumption.
  (* Uncaught Ltac2 exception: Tactic_failure (Some message:(No such assumption)) *)
  right. my_eassumption.
Qed.

(** Moreover, in case of [failure] it should trigger backtracking.
    We can check it works using [constructor].
*)

Goal nat -> False -> True \/ False.
  intros. constructor; print_goals; my_eassumption.
Qed.

(** You may be accustomed to use [fail], for example, if you are a Ltac1 user.
    In Ltac2, [fail] is easy to understand as it is literaly defined as
    [Control.enter (fun () => Control.zero (Tactic_failure None))].
    Therefore, [fail] is just failure raising the error [Tactic Failure]
    without any further error message.
    The [Control.enter] being to ensure it will not fail if there are no longer
    any goals to prove.
*)

Goal nat.
  Fail fail.
  Fail exact 0; Control.zero (Tactic_failure None).
  exact 0; fail.
Abort.

(** It is recommended to use [Control.zero] rather than [fail] to give nice
    error messages in case of failure.

    There is another primitive to raise exceptions [Control.throw : exn -> unit].
    The key difference with [zero] is that [throw] raises a non-catchable exception.
    It means that [throw] will not trigger backtracking.
    It will stop the computation all together.
*)

Goal nat -> False -> True \/ False.
  intros.
  (* This will not backtrack and try to prove [False] *)
  Fail constructor; print_goals; Control.throw (Tactic_failure None).
Abort.

(** Consequently, [throw] should only be used if one **really* wants to prevent backtracking. *)



(** ** 3. [Control.plus] to Catch Exceptions

    Since [Ltac2] has proper exceptions and backtracking is primitive, it is not
    only possible to catch exceptions, but also to backtrack upon them.

    The catching primitive is [Control.plus] of type [(unit -> 'a) -> (exn -> 'a) -> 'a].
    [Control.plus f k] installs a backtracking point around [f]:
    1. it tries all the success of [f], and if there are none, it tries [k]
    2. in case of subsequent failure, it backtracks to [f], and if all its
       successes have been exhausted, it tries the continuation [k] for next success.

    To understand [Control.plus], it can be useful to see it from the perspective of the stream model.
    Viewing [f] and [k] as stream of success -- ignoring exceptions for simplicity --
    then [Control.plus f k] is the concatenation of the two streams.
    Indeed, it applies the first success that works, so first checking [f] for one, then [k].
    In case of backtracking, it just try the next success in the stream, so once again,
    what is left to try in [f], then [k].

    *** 3.1 Reimplementing [+]

    To understand how [Control.plus] works in practice, let us define an "or" for
    tactics [tac1 ++ tac2], that should:
    1. Apply the first success of [tac1], and if there are none, try [tac2]
    2. In case of subsequent failure, backtrack to [tac1], and if all successes
       of [tac1] are exhausted, try [tac2]
    3. We want each of the focused goals to be tried independently

    This is a direct application of [Control.plus], as it consist in installing
    a backtracking point around [tac1], running [tac2 ()] in case of failure
    of [tac1] whatever the exception is raised.
    The whole thing being wrapped in [Control.enter] to focus the goals.
*)

Ltac2 or_backtrack (tac1 : unit -> unit) (tac2 : unit -> unit) : unit :=
  Control.enter (fun () =>
    Control.plus tac1 (fun _ => tac2 ())
  ).

(* Note that we need to specify thunk by hand with general notations *)
Ltac2 Notation tac1(thunk(self)) "++" tac2(thunk(self)) :=
  or_backtrack tac1 tac2.

(** Now that we have defined [++], let us tests it to ensure it works.
    That is important because it is easy to make mistakes when dealing with
    meta-programming, for instance to forget side cases.
*)

Goal exists n, n = 2 /\ n = 3.
  unshelve econstructor; only 2 : split.
    (* If the first tactic succeeds, it should be picked *)
  - (exact 2) ++ (exact 1).
    (* If the first tactic failed, the second should be picked *)
  - assumption ++ reflexivity.
    (* If none works, it should return the last error message *)
  - Fail assumption ++ (exact 4).
Abort.

(** In case of subsequent failure, it should backtrack to [tac1] until it has
    exhausted all its successes, in which case it should try [tac2]:
 *)

Goal exists n, n = 3.
  unshelve econstructor.
  (* The goals should be [1 = 3], [2 = 3], [3 = 3] *)
  all: only 1: ((exact 1) ++ (exact 2)) ++ (exact 3); print_goals; reflexivity.
Qed.

Goal (0 = 0 \/ 0 = 1) /\ (1 = 0 \/ 1 = 1).
  (* it picks [left] or [right] independently  *)
  split; Control.enter (fun _ => left ++ right); print_goals; reflexivity.
Abort.


(** ** 4. Using [Control.Case] to Inspect Backtracking

    [Control.plus] enables us to add a backtracking point to the backtracking structure.

    As a counterpart, we would like to be able to inspect the backtracking structure,
    to check if it is empty, that is, [Control.zero], or there is at least one success,
    and do something different in each case.

    To do so, we have the primitive [Control.case : (unit -> 'a) -> ('a * (exn -> 'a)) result],
    which given a thunk [h] returns either:
    1. an error [Err e] where [e] is an exception
    2. or a pair [Res (x,k)] where [x : 'a] is the first succes of [h], and
       [k : exn -> 'a] is the  backtracking continuation to try in case of subsequent failure.

    In the stream model, this basically consists in matching the stream checking
    if it is empty, and if not return the head with the rest of the stream.


  *** 4.1 Reimplement [||]

  As a first example where [Control.case] is needed, consider [++] or section 3.
  In practice, backtracking on [tac2] in case subsequent failure of the choice of [tac1]
  is not always wanted as it can make proof scripts costly, and hard to predict.

  If the script is of the form [tac1 ++ tac2; script], [script] will be
  repeated for every success of [tac1 ++ tac2], which can be costly.
  Moreover, [script] itself can backtrack leading to an exponential blow up of
  possibilities,  which is costly, but can also make it hard to predict what
  will be the goal in case of success.
*)

Goal exists (n m : nat), n = m.
  unshelve econstructor; only 2 : unshelve econstructor.
  all: only 1 : (exact 0) ++ (exact 1) ++ (exact 2);
       only 1 : (exact 10) ++ (exact 9) ++ (exact 2);
      print_goals ; reflexivity.
Qed.

(** Consequently, we would like a variant of the [++] tactical that
    applies the first tactics that succeeds, but will not backtrack to try
    [tac2] if it has chosen [tac1] and that leads to a subsequent failure.

    To do this, we use [Control.case] to check the backtracking structure of [tac1].
    1. If [tac1] fails, we try [tac2].
    2. If it succeeds, then we return [tac1], which we have to reconstruct with
       [Control.plus] as we have destructed it with [Control.Case].
    3. We wrapped it in [Control.enter] so that the choice is independent for
      every goal
*)

Ltac2 or_no_backtrack (tac1 : unit -> 'a) (tac2 : unit -> 'a) : 'a :=
  Control.enter (fun () =>
    match Control.case tac1 with
    | Err _ => tac2 ()
    | Val (x,k) => Control.plus (fun () => x) k
    end
  ).

(** Note that this is slightly different from Ltac1 usual [||] which also checks for
    progress on [tac1]
*)


(** Let us define an infix notation for it. *)

Ltac2 Notation tac1(thunk(self)) "||" tac2(thunk(self)) :=
  or_no_backtrack tac1 tac2.

(** We can now try the previous to tests that this still applies the first
    tactic that succeeds, but will not backtrack to [tac2] if [tac1] fails:
*)

Goal exists n, n = 2 /\ n = 3.
  unshelve econstructor; only 2 : split.
    (* If the first tactic succeeds, it should be picked *)
  - (exact 2) || (exact 1).
    (* If the first tactic failed, the second should be picked *)
  - assumption || reflexivity.
    (* If none works, it should fail returning the last error message *)
  - Fail assumption || (exact 4).
Abort.

Goal exists n, n = 3.
  unshelve econstructor.
  (* It picks [(exact 1) ++ (exact 2)] then [exact 1], it fails so backtracks
     to [exact 2] which fails, it stops here as it can not backtrack to [exact 3] *)
  Fail all: only 1: ((exact 1) ++ (exact 2)) || (exact 3); print_goals; reflexivity.
Abort.

(** If you are surprised by this example, remember, that all tactics are
      potentially backtracking by default. [||] does not disable this behaviour.
      It only prevents backtracking to [tac2] if [tac1] succeeded before.
*)



(** *** 4.2 Reimplement [once]

    Backtracking is allowed by default. To offer better control over it, the
    standard library of tactics offers the tactic combinator [once tac] that
    prevents [tac] from backtracking This enables us to have a fine-grained
    control.

    For instance, we can add [once] around [(exact 1) ++ (exact 2)] to prevent
    backtracking.
*)

Goal exists n, n = 2.
  unshelve econstructor.
  (* It picks [(exact 1) ++ (exact 2)], tries [tac1] and fails, but can not backtrack
      further to [exact 2] due to [once], hence backtrack to try [exact 3] *)
  Fail all: only 1: (once ((exact 1) ++ (exact 2))) ++ (exact 3); print_goals; reflexivity.
Abort.

(** Note, that [once (tac1 ++ tac2)] is not the same as [tac1 || tac2] ?
    The reason is that [once] prevents backtracking all together.
    However, [tac1 || tac2] only prevents backtracking to try [tac2], if [tac1] succeeded first.
    It does not prevent to backtrack to try [tac1] again.
    [once (tac1 ++ tac2)] actually corresponds to [once tac1 || once tac2].
*)

Goal exists n, n = 2.
unshelve econstructor.
(* this fails as no backtracking is allowed *)
Fail all: only 1: once (((exact 1) ++ (exact 2)) ++ (exact 3)); print_goals; reflexivity.
(* but this succeeds *)
all: only 1: ((exact 1) ++ (exact 2)) || (exact 3); print_goals; reflexivity.
Abort.


(** [once] can be coded easily with [Control.case] and [Control.zero].
    We inspect [tac] to check if it fails or produces a success.
    - If it fails, we return the original exception.
    - If it produces a success, we return the success, discarding the continuation
      to prevent backtracking.
*)

Ltac2 my_once0 (tac : unit -> 'a) : 'a :=
  match Control.case tac with
  | Err e => Control.zero e
  | Val(x,_) => x
  end.

Ltac2 Notation my_once := my_once0.

Goal exists n, n = 2.
  unshelve econstructor.
  (* It picks [(exact 1) ++ (exact 2)], tries [tac1] and fails, but can not backtrack
      further to [exact 2] due to [once], hence backtrack to try [exact 3] *)
  Fail all: only 1: (my_once ((exact 1) ++ (exact 2))) ++ (exact 3); print_goals; reflexivity.
Abort.

(** A common source of confusion using [Control.case] is to think that this
    will only try the first tactic.
    This is not the case: it applies the first tactic that succeeds.
    This is because [Control.case] returns the first success.

    For instance, if we try to solve [0 = 0] with [assumption ++ reflexivity]
    the first tactic to succeed is not [assumption] but [reflexivity], which
    will hence be picked by [Control.case (assumption ++ reflexivity)]:
*)

Goal (0 = 0).
  my_once (assumption ++ reflexivity).
Abort.

(** A logical question in now what does the below Ltac2 function [once_plus] do?
    It can seem weird at first to add a continuation to try in case of failure,
    and to use [once] and disable backtracking.
*)

Ltac2 once_plus (run : unit -> 'a) (handle : exn -> 'a) : 'a :=
  once (Control.plus run handle).

(** As [once] disable backtracking it is disable, nothing surpising there.
    The subtility is that as [Control.case] returns the first success, this
    adds more potential successes to try if [run] produces none, while
    preventing backtracking.
*)
