(** * How to write a contradiction tactic with Ltac2

  *** Authors
  - Thomas Lamiaux

  *** Summary

  This tutorial explains how to write a variant of the [contradiction] tactic using Ltac2.
  In particular, it showcases how to use [match! goal] and choose among [lazy_match!]
  or [match!] and shows how to use quoting, and the Constr and Ind API to check properties on inductive types.

  *** Table of content

  - 1. Introduction
  - 2. Matching the goal for [P] and [~P]
    - 2.1 Choosing [lazy_match!], [match!] or [multi_match!]
    - 2.2 Matching Syntactically or Semantically
    - 2.3 Error messages
  - 3. Using Constr.Unsafe and Ind API to Add Syntactic Checks
    - 3.1 Checking for Empty and Singleton Types
    - 3.2 Checking for Empty and Singleton Hypotheses
  - 4. Putting it All Together

  *** Prerequisites

  Disclaimer:

  Needed:
  - Basic knowledge of Ltac2

  Installation:
  - Ltac2 and its core library are available by default with Rocq

*)

From Ltac2 Require Import Ltac2 Constr Printf.

(** ** 1. Introduction

    We write a variant of the [contradiction] tactic up to small differences.
    The overall specification of [contradiction] is that it can take an argument or not:

    If [contradiction] does not take an argument, then [contradiction]:
    1. First introduces all the variables,
    2. Tries to prove the goal by checking the hypotheses for:
      - A pair of hypotheses [p : P] and [np : ~P], such that any goal can be
        proven by [destruct (np p)]
      - An hypothesis [x : T] where [T] is an inductive type without any constructor
        like [False], in which case [destruct x] solves the current goal
      - An hypothesis [nx : ~T] such that [T] is an inductive type with
        one constructor without arguments, like [True] or [0 = 0];
        in other words, such that [T] is provable by [constructor 1].

    If [contradiction] takes an argument [t] then, the type of [t] must either be:
    1. An empty inductive type like [False], in which case the goal is proven
    2. Or a negation [~P], in which case:
        - If there is a hypothesis of type [P] in the context, then the goal is proven;
        - otherwise, the goal is replaced by [P].

    In this how-to we will see how to write it using Ltac2.

*)

(** ** 2. Matching the goal for [P] and [~P]

    *** 2.1 Choosing [lazy_match!], [match!] or [multi_match!]

    To look up for a pair of hypotheses [P] and [~P], we need to match the goal.
    There are three commands to match the goal that have different behaviour
    regarding backtracking. The first step is to understand which one we want to use.

    - [lazy_match! goal with] picks a branch, and sticks to it to even if the code
      executed after picking this branch (the body of the branch) leads to a failure.
      In practice, it is sufficient for all applications where matching the syntax
      is enough and deterministic.

    - [match! goal with] that picks the first branch that succeeds, but further backtracks
      to its choice if the evaluation of its body fails to pick another matching branch,
      potentially the same one if all the hypotheses have not been exhausted yet.
      [match!] is useful as soon as matching the syntax is not enough, and we
      need additional tests to see if we have picked the good hypotheses or not.

    - [multi_match! goal with] that behaves like [match!] except that it will
      further backtrack if its choice of a branch leads to a subsequent failure
      when linked with another tactic.
      [multi_match!] is meant to write tactics performing a choice, and that
      we want to link with other tactics, like the [constructor] tactic.
      The [contradiction] tactics is meant to solve goals with a simple enough
      inconsistent context. It is not meant to be linked with other tactics.
      Consequently, we have no use for [multimatch!] to implement [contradiction].

    Choosing betwen [lazy_match!] and [match!] really depends if we need
    more than a syntax check as we will see in the rest of this how-to guide.
*)


(** *** 2.2 Matching Syntactically or Semantically *)

(** Whether we choose to use [lazy_match!] or [match!], there are different
    ways to match for [P] and [~P]. We can match the syntax directly, or match
    it semantically that is up to some reduction, conversion or unification.

    This different options have different levels of expressiveness, allowing them
    to match hypotheses to varying degrees. They also have different cost and side
    effects, for instance, conversion does not unify evariables opposite to unify.

    Understanding which strategy to choose is not easy. We will now discuss
    the different options, and their pros and cons, before choosing one.


    **** 2.2.1 Matching Syntactically

    Except for non-linear matching, matching is by default syntactic.
    That is, terms are matched and compared only up to α-conversion and evar expansion.
    To match for [P] and [~P], we can use the pattern [p : ?t, np : ~(?t)].
    In this pattern, [t] is non-linear so it will be matched up to conversion.
    However, matching for a term of the form [~(_)] will be syntactically,
    i.e. up to α-conversion.

    If we have found hypotheses [P] and [~P], then we can prove [False].
    Consequently, this is deterministic and we can use [lazy_match!] for it.
*)

Goal forall P Q, P -> ~Q -> ~P -> False.
  intros.
  lazy_match! goal with
  | [p : ?t, np : ~(?t) |- _ ] => printf "Hypotheses are %I,%I,%t" p np t
  | [ |- _ ] => printf "There are no hypotheses left to try"; fail
  end.
Abort.

(** Once we have found [P] and [~P], we want to prove [False] using the usual
    [destruct] tactic that expects a Rocq term, that is we want to write [destuct (np p)].
    However, this is not possible as though, as [p : ident] and [np : ident] are
    identifiers, i.e. the name of the hypotheses [P] and [~P], wheras [destruct X]
    expects [X] to be a Rocq term.

    To get the terms associated to [p] and [np], we must use [Control.hyp : ident -> contr],
    which transforms an [ident] corresponding to an hypothesis into a Rocq term
    we can manipulate in Ltac2, that is, into an object of type [constr].
    If there are no such hypotheses then it raises an error.
    For [p] and [np], this gives us:

    [[  let p := Control.hyp p in
        let np := Control.hyp np in
        ...
    ]]

    Once, we have gotten the term associated to the hypotheses with [Control.hyp],
    we must go back to Rocq's world to be able to use [destruct].
    We do so with [$], which leads to:

    [[
      let p := Control.hyp p in
      let np := Control.hyp np in
      destruct ($np $p)
    ]]

    Notation, to do [Control.hyp] and [$] at once is only available in Rocq 9.1 or above.

    This leads us to the following script:
*)

Ltac2 match_PnP_syntax () :=
  lazy_match! goal with
  | [p : ?t, np : ~(?t) |- _ ] =>
        printf "Hypotheses are %I,%I,%t" p np t;
        let p := Control.hyp p in
        let np := Control.hyp np in
        destruct ($np $p)
  | [ |- _ ] => printf "There are no hypotheses left to try"; fail
  end.

Goal forall P Q, P -> ~Q -> ~P -> False.
  intros. match_PnP_syntax ().
Qed.

Goal forall P, P -> (P -> nat) -> False.
  intros. Fail match_PnP_syntax ().
Abort.

(** It has the advantage to be fast but the downside is that it will not match
    [?t -> False], even though it is convertible to [~(?t)], as [~(_)] is
    match syntactically.
    It is not what we want for a [contradiction] tactic.
*)

Goal forall P, P -> (P -> False) -> False.
  intros. Fail match_PnP_syntax ().
Abort.

(** To deal with [?t -> False], we could be tempted to add an extra-pattern in
    the definition, but this would not scale as any variations around [~] would fail.
*)

Goal forall P, P -> ((fun _ => ~P) 0) -> False.
  intros. Fail match_PnP_syntax ().
Abort.

(** Checking terms up to syntax is not a good notion of equality in type theory.
    For instance, [4 + 1] is not syntactically equal to [5].
    What we really want here is to compare type semantically, i.e. up to
    some reduction, conversion or unification.
*)

(** Note, however, that it would match [~((fun _ => P) 0)] as [t] in [~t] is
    matched up to conversion.
*)

Goal forall P, P -> ~ ((fun _ => P) 0) -> False.
  intros. match_PnP_syntax ().
Abort.

(** **** 2.2.2 Matching up to Unification

    Before considering finer ways to compare terms semantically, let us first
    consider how to match terms up to unification as it is what comes up
    first to mind when trying to write meta-programming.

    To match semantically, we must match for a pair of hypotheses
    [p : ?t1, np : ?t2 |- _], then check that [t2] is of the form [t1 -> False].
    Something fundamental to understand, here, is that with this approach the
    syntax check is no longer sufficient to be able to prove [False], as we match
    for any pair of hypotheses then check we have picked the good ones.
    We hence need to switch from [lazy_match!] to [match!] to be able to
    backtrack and try the next hypotheses, if we have picked the wrong ones.

    To unify the types, we can exploit that tactics do unification.
    For instance, we can ensure that [t2] is of the shape [t1 -> X] by applying
    [$np] to [$p]; i.e. [$np $p], as otherwise it would be ill-typed.
    We also need to ensure that [X] is [False], otherwise, [destruct ($np $p)]
    could do pattern matching on [nat] which would not solve the goal.
    We can ensure that it does solve the goal by wrapping it in [solve].
    However, it is not an efficient solution, as we would still do [destruct] for
    every pair of hypotheses until we found one that works, which can be costly.
    A better solution, is to use a type annotation [$np $p :> False] to force the
    type of [$np $p] to be [False].

    This leads to the script:
*)

Ltac2 match_PnP_unification_v1 () :=
  match! goal with
  | [p : ?t1, np : ?t2 |- _ ] =>
        printf "Hypotheses are %I : %t, and %I : %t" p t1 np t2;
        let p := Control.hyp p in
        let np := Control.hyp np in
        destruct ($np $p :> False)
  | [ |- _ ] => printf "There are no hypotheses left to try"; fail
  end.

Goal forall P Q, P -> ~Q -> ~P -> False.
  intros. match_PnP_unification_v1 ().
Qed.

Goal forall P, P -> (P -> nat) -> False.
  intros. Fail match_PnP_unification_v1 ().
Abort.

Goal forall P, P -> (P -> False) -> False.
  intros. match_PnP_unification_v1 ().
Qed.

Goal forall P, P -> ((fun _ => ~P) 0) -> False.
  intros. match_PnP_unification_v1 ().
Qed.

(** While this technically works, a better and more principled approach is to
    directly use the primitive [Std.unify : constr -> constr -> unit] that
    that unifies two terms, and raises an exception if it is not possible.

    With this approach, there are much less chances to make an error,
    like misunderstanding how unification is done by the tactics, or
    forgetting the type annotation [:> False].

    Moreover, it scales much better. Conversion is only available for
    Rocq 9.1 and later versions, so we will not utilize it in this how-to guide.
    However, if it were available, we could essentially replace [Std.unify]
    with [Std.conversion] to obtain the alternative version.
    One could even consider parametrising the code by a check that could later
    be instantiated with unification, conversion or some syntax check up to
    reduction, like to the head normal form.
*)

Ltac2 match_PnP_unification_v2 () :=
  match! goal with
  | [p : ?t1, np : ?t2 |- _ ] =>
        printf "Hypotheses are %I : %t, and %I : %t" p t1 np t2;
        Std.unify t2 '($t1 -> False);
        printf "Unification Worked!";
        let p := Control.hyp p in
        let np := Control.hyp np in
        destruct ($np $p)
  | [ |- _ ] => printf "There are no hypotheses left to try"; fail
  end.

Goal forall P Q, P -> ~Q -> ~P -> False.
  intros. match_PnP_unification_v2 ().
Qed.

Goal forall P, P -> (P -> nat) -> False.
  intros. Fail match_PnP_unification_v2 ().
Abort.

Goal forall P, P -> (P -> False) -> False.
  intros. match_PnP_unification_v2 ().
Qed.

Goal forall P, P -> ((fun _ => ~P) 0) -> False.
  intros. match_PnP_unification_v2 ().
Qed.

(** An issue with unification is that it can unify evariables.
    For instance [match_PnP_unification_v2] can solve the following goal
    which is not the case for the usual [contradiction] tactic.
*)

Goal forall P Q, P -> ~Q -> False.
  intros. eassert (X4 : _) by admit.
  match_PnP_unification_v2 ().
Abort.

(** This is costly, but also not a very good practice for automation tactics
    which should not unify evariables behind the scene as it can
    unify them in an unexpected way getting the users stuck later.
    Users should have control on whether evariables are unified or not, hence
    the different e-variants like [assumption] and [eassumption].
*)

(** **** 2.2.3 Matching up to Reduction

    To have finer control on what happens and reduce the cost of unification,
    we can instead reduce our types to a head normal form to check it is of the
    form [X -> Y] as [->] is an infix notation, (it should be seen as [-> X Y]).
    We can then check that [X] is [t1], and [Y] is [False].

    To reduce terms, there are many primitives in [Std]. We want to reduce to the
    head normal form so we can use directly [Std.eval_hnf : constr -> constr].
    We can then match the head with [lazy_match!] with the pattern [?x -> ?y].
    We use [lazy_match!] as this is deterministic, either our term is a product
    or it is not.

  [[
    match! goal with
    | [p : ?t1, np : ?t2 |- _ ] =>
          let t2' := Std.eval_hnf t2 in
          lazy_match! t2' with
          | ?x -> ?y => printf "(%I : %t) is a product %t -> %t" np t2 x y;
          | _ => printf "(%I : %t) is not product" np t2;
          end
    | [ |- _ ] => printf "There are no hypotheses left to try"; fail
  ]]

    We then have to compare [X] with [t1], and [Y] with [False]. We would like to
    compare terms up to conversion as it is reasonably inexpensive, but still
    very expressive. Unfortunately, there is no primitive for it at the moment.

    Consequently, we compare them up to syntactic equality which is still very
    expressive when combined with reduction using [Constr.equal : term -> term -> bool].
    This gives us the following script to which we add some printing functions
    to see what is going on.
*)

Ltac2 match_PnP_unification_v3 () :=
  match! goal with
  | [p : ?t1, np : ?t2 |- _ ] =>
        printf "Hypotheses are %I : %t, and %I : %t" p t1 np t2;
        lazy_match! (Std.eval_hnf t2) with
        | ?x -> ?y =>
            printf "(%I : %t) is a product %t -> %t" np t2 x y;
            if Bool.and (Constr.equal (Std.eval_hnf x) t1)
                        (Constr.equal (Std.eval_hnf y) 'False)
            then printf "(%I : %t) is a contradiction of (%I : %t)" np t2 p t1;
                 let p := Control.hyp p in
                 let np := Control.hyp np in
                 destruct ($np $p)
            else (printf "(%I : %t) is not a contradiction of (%I : %t)" np t2 p t1;
                  printf "----- Backtracking -----"; fail)
        | _ => printf "(%I : %t) is not product" np t2;
               printf "----- Backtracking -----"; fail
        end
  | [ |- _ ] => printf "There are no hypotheses left to try"; fail
  end.

Goal forall P Q, P -> ~Q -> ~P -> False.
  intros. match_PnP_unification_v3 ().
Qed.

Goal forall P, P -> (P -> nat) -> False.
  intros. Fail match_PnP_unification_v3 ().
Abort.

Goal forall P, P -> (P -> False) -> False.
  intros. match_PnP_unification_v3 ().
Qed.

Goal forall P, P -> ((fun _ => ~P) 0) -> False.
  intros. match_PnP_unification_v3 ().
Qed.

(** However, this now fails as evariables are no longer unified. *)

Goal forall P Q, P -> ~Q -> False.
  intros. eassert (X4 : _) by admit.
  Fail match_PnP_unification_v3 ().
Abort.

(** **** 2.2.4 Optimisation

    Using reduction already provides us with a fine control over what is going on
    but is still a bit inefficient as we try to compare every pair of hypotheses.
    Instead, we can look for a negation [~P], and only if found check
    for an hypothesis [P]. This basically amounts to spliting the match in
    two parts. As it can be seen, it matches much fewer hypotheses in case of failure.
*)

Ltac2 match_PnP_unification_v4 () :=
  match! goal with
  | [np : ?t2 |- _ ] =>
      printf "Hypothesis is %I : %t" np t2;
      let np := Control.hyp np in
      (* Check [t2] is a negation ~P *)
      lazy_match! (Std.eval_hnf t2) with
      | ?x -> ?y =>
        if Constr.equal (Std.eval_hnf y) 'False then
          printf "%t is a negation %t -> %t" t2 x y;
          printf "Search for %t:" x;
          printf "    ------------------------";
          (* Check for an hypothesis P *)
          match! goal with
          | [p : ?t1 |- _ ] =>
            printf "    Hypothesis is %I : %t" p t1;
            if Constr.equal (Std.eval_hnf x) t1
            then printf "    %t is a contradiction of %t" t2 t1;
                 let p := Control.hyp p in destruct ($np $p)
            else (printf "    ----- Backtracking -----"; fail)
          | [ |- _ ] => printf "    There are no hypotheses left to try";
                        printf "----- Backtracking -----"; fail
          end
        else ( printf "%t is not a negation" t2;
               printf "----- Backtracking -----"; fail)
      | _ => printf "%t is not a negation" t2;
             printf "----- Backtracking -----"; fail
      end
  | [ |- _ ] => printf "Failure: There are no hypotheses left to try"; fail
  end.

Goal forall P Q, P -> ~Q -> ~P -> False.
  intros. match_PnP_unification_v4 ().
Qed.

Goal forall P, P -> (P -> nat) -> False.
  intros. Fail match_PnP_unification_v4 ().
Abort.

Goal forall P, P -> (P -> False) -> False.
  intros. match_PnP_unification_v4 ().
Qed.

Goal forall P, P -> ((fun _ => ~P) 0) -> False.
  intros. match_PnP_unification_v4 ().
Qed.

Goal forall P Q, P -> ~Q -> False.
  intros. eassert (X4 : _) by admit.
  Fail match_PnP_unification_v4 ().
Abort.

(** *** 2.3 Error Messages

  So far, we have been using [fail] to trigger failure, which returns
  the error message [Tactic_failure None].

  We can be finer using the primitive [Control.zero : exn -> 'a] to raise an error.
  We can then raise a custom error message using [Tactic_failure : message option -> exn]
  that raises an error for any given message.
  We can then write complex error message using [fprintf] that behaves as [printf]
  excepts that it returns a [message] rather than printing it.
*)

Goal forall P, P -> (P -> nat) -> False.
  Fail match! goal with
  | [ |- _ ] => Control.zero (Tactic_failure (Some (fprintf "No such contradiction")))
  end.
Abort.

(** The error type [exn] is an open type, which mean we can add a constructor to it,
    i.e. a new exception, at any point.
    We can hence create a new exception just for [contradiction].
*)

Ltac2 Type exn ::= [ Contradiction_Failed (message option) ].

Goal forall P, P -> (P -> nat) -> False.
  Fail match! goal with
  | [ |- _ ] => Control.zero (Contradiction_Failed (Some (fprintf "No such contradiction")))
  end.
Abort.


(** ** 3. Using Constr.Unsafe and Ind API to Add Syntactic Checks

    We need to check for hypotheses that are either empty like [False], or
    of form [~t] where [t] is an inductive type with one constructor without
    arguments like [nat] or [0 = 0] that we can prove with [constructor 1].

    We can do so very directly by trying to solve the goal assuming we have
    found the good hypotheses wrapping it in [solve] to ensure that it works.
    In this case, for [p : t] and [np : ~t] that would mean doing
    [solve [destruct $p]] and [destruct ($np ltac2:(constructor 1))].
    However, that would be very inefficient as we would [destruct] any hypothesis, which can be expensive.

    A better approach is to add a syntax check that verifies that [t] is of the
    appropriate form. It is much cheaper as it is basically matching syntax.
    We can do so by using the API [Constr.Unsafe] that enables to access the
    internal syntax of Rocq terms, and [Ind] to access inductive types.

    The API "unsafe" is named this way because as soon as you start manipulating
    internal syntax, there is no longer any guarantee you create well-scoped terms.
    Here, we will only use it to match the syntax so there is nothing to worry about.
*)

(** *** 3.1 Checking for Empty and Singleton Types

    In both cases, the first step is to check if the term is an inductive type.
    Internally, a type like [list A] is represented as [App (Ind ind u) args]
    where [ind] is the name of the inductive and the position of the block,
    and [u] represents universe constraints.
    Consequently, given a [t : constr] we need to decompose the application
    [App x args], then match [x] for [Ind ind u].

    This can be done using [Unsafe.kind : constr -> kind] which converts a
    [constr] to a shallow embedding of the internal syntax, which is defined
    as a Ltac2 inductive type [kind].
    [kind] is a shallow embedding which means a [constr] is not fully
    converted to a representation of the internal syntax, only its head.
    For example, the type of [Unsafe.App] is [constr -> constr array -> kind].
    That is, [u] and [v] in [Unsafe.App u v] remain regular [constr] elements
    and are not recursively converted to [kind], which characterizes it as shallow.
    In contrast, if we had a deep embedding, the arguments of [Unsafe.App] would be
    recursively converted to [kind], resulting in the type [kind -> kind array -> kind].
    The reason for using a shallow embedding is that it is much faster than fully
    converting terms to the internal syntax, yet sufficient for most applications.

    Let us first write a function [decompose_app] that translates a [constr] to
    [kind], then match it for [Unsafe.App] and returns the arguments.
    It is already available starting Rocq 9.1, but it still is good to recode it.

    There are two things to understand here:
    - 1. We match [kind] using [match] and not with [match!] as [kind] is an
         inductive type of Ltac2. [match!] is to match [constr] and goals.
    - 2. We really need the shallow embedding: we cannot match the type of a
         term as we did for [X -> Y]. Indeed, we can match [X -> Y] with [match!]
         as we know there are exactly 2 arguments, so the syntax is fully specified.
         In constrasts, an application like an inductive type could have arbitrary
         many arguments, and we can hence not match it with [match!]
*)

Ltac2 decompose_app (t : constr) :=
  match Unsafe.kind t with
    | Unsafe.App f cl => (f, cl)
    | _ => (t,[| |])
  end.

(** Getting the inductive data associated to an inductive block is similar.
    We first use [decompose_app] to recover the left side of the application,
    we then convert to the syntax to check if it is an inductive, in which case
    we recover the inductive definition with [Ind.data : inductive -> data].

    A subtlety to understand is that [Unsafe.kind] converts the syntax without
    reducing terms. So if we want [(fun _ => True) 0] to be considered as an
    inductive, we need to reduce it first to a head normal form with
    [Std.eval_hnf : constr -> constr].
 *)

Import Ind.

Ltac2 get_inductive_body (t : constr) : data option :=
  let (x, _) := decompose_app (Std.eval_hnf t) in
  match Unsafe.kind (Std.eval_hnf x) with
  | (Unsafe.Ind ind _) => Some (Ind.data ind)
  | _ => None
  end.

(** We are ready to check if a type is empty or not, which is now fairly easy.
    Given the definition of an inductive type, it suffices to get the number
    of constructor with [nconstructors : data -> int], and check it is zero.
*)

Ltac2 is_empty_inductive (t : constr) : bool :=
 match get_inductive_body t with
 | Some ind_body => Int.equal (Ind.nconstructors ind_body) 0
 | None => false
 end.

(** We can check an inductive type is a singleton similarly, except to one small issue.
    The primitive to access the arguments of a constructor is only available in
    Rocq 9.1 or above. So for now, we will hence only check that it has only one constructor.
    Though this is not perfect and forces us to wrap [destruct ($np ltac2:(constructor 1)]
    in [solve], it still rules out most inductives like [nat].
*)

Ltac2 is_singleton_type (t : constr) : bool :=
  match get_inductive_body t with
  | Some ind_body => Int.equal (Ind.nconstructors ind_body) 1
  | None => false
  end.

(** *** 3.2 Checking for Empty and Singleton Hypotheses

    Writing a tactic to check for empty hypothesis is now fairly easy.
    We just match the goal using [match!] as the syntax check is not complete,
    then check if it is empty, and if it is, prove the goal with [destruct $p].
*)

Ltac2 match_P_empty () :=
  match! goal with
  | [ p : ?t |- _ ] =>
        let p := Control.hyp p in
        if is_empty_inductive t then destruct $p else fail
  | [ |- _ ] => Control.zero (Contradiction_Failed (Some (fprintf "No such contradiction")))
  end.

Goal False -> False.
  intros. match_P_empty ().
Qed.

Goal True -> False.
  intros. Fail match_P_empty ().
Abort.

(** Checking for the negation of an inductive type is a little bit more involved
    as we need to check the type of [?] is of the form [?X -> False].
    We can do so by creating a fresh evariable of type [Type] with
    [open_constr:(u :> Type)] then using [Std.unifiy]:
*)

Ltac2 match_nP_singleton () :=
  match! goal with
  | [ np : ?t2 |- _ ] =>
      let np := Control.hyp np in
      lazy_match! (Std.eval_hnf t2) with
      | ?x -> ?y =>
        if Bool.and (is_singleton_type x) (Constr.equal (Std.eval_hnf y) 'False)
        then solve [destruct ($np ltac2:(constructor 1))]
        else printf "%t is not a singeleton or %t is not False" x y ; fail
      | _ => printf "%t is not product" t2; fail
      end
  | [ |- _ ] => Control.zero (Contradiction_Failed (Some (fprintf "No such contradiction")))
  end.

Goal ~True -> False.
  intros. match_nP_singleton ().
Qed.

Goal ~(0 = 0) -> False.
  intros. match_nP_singleton ().
Qed.

Goal ~(0 = 1) -> False.
  intros. Fail match_nP_singleton ().
Abort.

(** ** 4. Putting it All Together *)

(** It took a few explanations, but in the end the code of [contradiction_empty]
    is rather short using Ltac2.

    To be efficient, we first perform the syntax check as it is very cheap.
    We hence first check for an empty hypotheses, then if it is a negation,
    in particular of a singletion inductive type. If it is none of these,
    check for [P] and [~P] which we perform last in order not to check
    the whole context for nothing.
*)

Ltac2 contradiction_empty () :=
  intros;
  match! goal with
  | [np : ?t2 |- _ ] =>
      let np := Control.hyp np in
      (* Check if [t2] is empty  *)
      if is_empty_inductive t2 then destruct $np else
      (* If it is not, check if [t2] is a negation ~P *)
      lazy_match! (Std.eval_hnf t2) with
      | ?x -> ?y =>
          if Constr.equal (Std.eval_hnf y) 'False then
            (* If so check if [x] is empty *)
            if is_singleton_type x
            then solve [destruct ($np ltac2:(constructor 1))]
            (* If not, check for an hypothesis P *)
            else (match! goal with
              | [p : ?t1 |- _ ] =>
                if Constr.equal (Std.eval_hnf x) t1
                then let p := Control.hyp p in destruct ($np $p)
                else fail
              | [ |- _ ] => fail
            end)
          else fail
      | _ => fail
      end
  | [ |- _ ] => fail
  end.

(** We also need to write a [contradiction] when it takes an argument. *)

Ltac2 contradiction_arg (t : constr) :=
  lazy_match! (Std.eval_hnf (type t)) with
  | ?x -> ?y =>
      if Constr.equal (Std.eval_hnf y) 'False
      then match! goal with
        | [p : ?t1 |- _ ] =>
            if Constr.equal (Std.eval_hnf x) t1
            then let p := Control.hyp p in destruct ($t $p)
            else fail
        | [ |- _ ] => assert (f : False) > [apply $t | destruct f]
        end
      else fail
  | _ => Control.zero (Contradiction_Failed (Some (fprintf "%t is not a negation" t)))
  end.

Goal forall P, P -> ~P -> 0 = 1.
  intros P p np. contradiction_arg 'np.
Qed.

Goal forall P, ~P -> 0 = 1.
  intros P np. contradiction_arg 'np.
Abort.

Goal forall P, P -> 0 = 1.
  intros P p. Fail contradiction_arg 'p.
Abort.

(** Finally, we define a wrapper for it :  *)

Ltac2 contradiction0 (t : constr option) :=
  match t with
  | None => contradiction_empty ()
  | Some x => contradiction_arg x
  end.

(** We can now use [contradiction0] directly writing [None] and [Some], and
    the quoting constructor by hand.
*)

Goal forall P Q, P -> ~Q -> ~P -> False.
  contradiction0 None.
Qed.

Goal forall P, P -> ~P -> 0 = 1.
  intros P p np. contradiction0 (Some 'np).
Qed.

(** Alternatively, we can define a notation to do deal insert [None], [Some] and
    the quoting for us, but be aware it may complicate parsing.
*)

Ltac2 Notation "contradiction" t(opt(constr)) := contradiction0 t.

Goal forall P Q, P -> ~Q -> ~P -> False.
  contradiction.
Qed.

Goal forall P, P -> ~P -> 0 = 1.
  intros P p np. contradiction np.
Qed.

(** Finally, just to be sure everything is alright, let us check [contradiction]
    on all the examples we have seen so far.
*)

(* pairs of hypotheses *)
Goal forall P Q, P -> ~Q -> ~P -> False.
  contradiction.
Qed.

Goal forall P, P -> (P -> nat) -> False.
  Fail contradiction.
Abort.

Goal forall P, P -> (P -> False) -> False.
  contradiction.
Qed.

Goal forall P, P -> ((fun _ => ~P) 0) -> False.
  contradiction.
Qed.

Goal forall P Q, P -> ~Q -> False.
  intros. eassert (X4 : _) by admit.
  Fail contradiction.
Abort.

(* empty hypotheses *)
Goal False -> False.
  contradiction.
Qed.

Goal True -> False.
  Fail contradiction.
Abort.

(* Negation of a singleton *)
Goal ~True -> False.
  contradiction.
Qed.

Goal ~(0 = 0) -> False.
  contradiction.
Qed.

Goal ~(0 = 1) -> False.
  Fail contradiction.
Abort.

(* negation given as an argument *)
Goal forall P, P -> ~P -> 0 = 1.
  intros P p np. contradiction np.
Qed.

Goal forall P, ~P -> 0 = 1.
  intros P np. contradiction np.
Abort.

Goal forall P, P -> 0 = 1.
  intros P p. Fail contradiction p.
Abort.