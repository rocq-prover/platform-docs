(** * Tutorial Ltac2 : Matching Terms and Goals

  *** Authors
  - Thomas Lamiaux

  *** Summary

  Ltac2 has native support to match the structure of terms, and of the goal,
  making it easy to build decision procedures or solvers.
  There are three primitives to match terms or goals [lazy_match!], [match!],
  and [multi_match!], which only differ by their backtracking abilities.
  (Not to be confused with [match] which is for Ltac2 inductive types.)
  Consequently, we first explain how matching terms and goals work using
  [lazy_match!], then discuss the backtracking differences in a third section.

  *** Table of content

  - 1. Matching Terms
    - 1.1 Basics
    - 1.2 Non-Linear Matching
  - 2. Matching Goals
    - 1.1 Basics
    - 1.2 Non-Linear Matching
  - 3. Backtracking and [lazy_match!], [match!], [multi_match!]
    - 3.1 [lazy_match!]
    - 3.2 [match!]
    - 3.3 [multi_match!]

  *** Prerequisites

  Disclaimer:

  Needed:
  - Basic knowledge of Ltac2

  Installation:
  - Ltac2 and its core library are available by default with Rocq.
*)

(** Let us first import Ltac2, and write a small function printing the goal under focus. *)
From Ltac2 Require Import Ltac2 Constr Printf.
Import Bool.BoolNotations.

Ltac2 print_goals0 () :=
  Control.enter (fun () =>
  match! goal with
  [ |- ?t] => printf "the goal is %t" t
  end
  ).

Ltac2 Notation print_goals := print_goals0 ().

(** ** 1 Matching terms

    *** 1.1 Basics

    Ltac2 has primitives to match a term to inspect its shape, for instance,
    if it is a function or a function type.
    This enables to perform different actions depending on the shape of the term.

    To match a term, the syntax is [lazy_match! t with] with one clause of
    the form [ ... => ...] per pattern to match.
    As an example, let's write a small function proving the goal provided
    it is given an argument of type [True -> ... -> True -> False].

    We write a recursive function that matches the type of [t] obtained with
    [Constr.type : constr -> constr] against [False] and [True -> _].
    In the first case, we prove the goal with [destruct $t], in the second
    case we recursively attempt to solve the goal with [triv '($t I)] by
    applying [t] to the only inhabitant of [True], [I : True].
*)

Ltac2 rec triv (t : constr) :=
  lazy_match! Constr.type t with
  | False => destruct $t
  | True -> _ => triv '($t I)
  end.

Goal False -> True.
  intros H. triv 'H.
Abort.

Goal (True -> True -> True -> False) -> True.
  intros H. triv 'H.
Abort.

Goal True -> True.
  intros H. Fail triv 'H.
Abort.

(** As in Rocq, the default pattern is a wildcard [_], that will match anything.
    It is practical to do something specific if the term matched is of any other
    shape than the one matched.
    For instance, we can use it to return a more specific error than
    [Match_failure] by defining [err_triv] to return if it fails.
*)

Ltac2 err_triv t := Control.zero (Tactic_failure (Some (
    fprintf "%t is not of the form True -> ... -> True -> False" t
  ))).

Ltac2 rec triv_err (t : constr) :=
  let ty := Constr.type t in
  printf "the type under consideration is %t" ty;
  lazy_match! ty with
  | False => destruct $t
  | True -> _ => triv_err '($t I)
  | _ => err_triv ty
  end.

Goal True -> True.
  intros H. Fail triv_err 'H.
Abort.

(** In some cases, we do not want to merely match the shape of a term [t],
    but also to recover a part of this subterm to perform more actions on it.
    This can be done using variables which must be written [?x].
    In such cases, [x] is of type [constr], the type of Rocq terms in Ltac2.
    This is normal as [x] corresponds to a subterm of [t].

    Note that as in OCaml, variable names cannot start with an upper case letter as this
    is reserved for constructors of inductive types.

    As an example consider writing a boolean (in Ltac2, not in Rocq) test to check if a type is a
    proposition written out of [True], [False], [~] ,[/\] ,[\/].
    To check a term is a proposition, we need to match it to inspect its head symbol,
    and if it is one of the allowed ones check its subterms also are propositions.
    Consequently, we need to remember subterms, and to match [/\] we need to
    use the pattern [?a /\ ?b]. This gives the following recursive function:
*)

Ltac2 rec is_proposition (t : constr) :=
  lazy_match! t with
  | True => true
  | False => true
  | ?a /\ ?b => is_proposition a && is_proposition b
  | ?a \/ ?b => is_proposition a && is_proposition b
  | _ => false
  end.

(** To test it, let us write a small printing function. *)
Ltac2 check_is_proposition (t : constr) :=
  if is_proposition t
  then printf "%t is a proposition" t
  else printf "%t is not a proposition" t.

Goal (True \/ (True /\ False)) -> nat -> True.
  intros H1 H2.
  check_is_proposition (Constr.type 'H1).
  check_is_proposition (Constr.type 'H2).
Abort.


(** ** 1.2 Non-Linear Matching

    Matching of syntax is by default syntactic. It means terms are only inspected
    to be of the appropriate shape up to α-conversion and expansion of evars.

    For instance, [fun x => x] and [fun y => y] are equal syntactically as they
    only differ by their names of bound variables (α-conversion), but [1 + 4]
    and [5] are not equal syntactically as they are only equal up to reduction.
    As a consequence, a small variation around a term that would require a
    reduction step like [(fun _ => False) 0] will not be matched by [False].
*)

Goal ((fun _ => False) 0) -> False.
  intros H. Fail triv_err 'H.
Abort.

(** In Ltac2, it is up to the users to reduce the terms appropriately before matching them.
    In most cases, we match the syntax to find what is the head symbol [False]
    or [->], in which case it suffices to compute the head normal form (hnf)
    with [Std.eval_hnf : constr -> constr].
    With extra-printing to show the difference before and after [eval_hnf],
    this gives us this barely different version of [triv_err].
*)

Ltac2 rec triv_hnf (t : constr) :=
  let ty := Constr.type t in
  printf "the type under consideration is %t" ty;
  let ty_hnf := Std.eval_hnf ty in
  printf "the hnf type under consideration is %t" ty_hnf;
  lazy_match! ty_hnf with
  | False => destruct $t
  | True -> _ => triv_hnf '($t I)
  | _ => err_triv ty_hnf
  end.

Goal (True -> ((fun _ => False) 0)) -> True.
  intros H. triv_hnf 'H.
Abort.

Goal (True -> (((fun _ => True) 0) -> True -> False)) -> True.
  intros H. triv_hnf 'H.
Abort.

(** The advantage of this approach is that the default is fast and predictable,
    and full control is left to the user to compare terms up to the notion of
    their choosing like up to head-normal form, or up to unification.

    This explains how syntax is matched but not how a pattern is matched when a
    variable [?x] appears more than once in a pattern, like [?x = ?x].
    Such patterns are called non-linear, and are matched up to conversion.
    The reason is that we expect the subterms matched to be the same,
    which in type theory naturally corresponds to conversion.
*)

Ltac2 is_refl_eq (t : constr) :=
  lazy_match! t with
  | ?x = ?x => printf "it is a reflexive equality"
  | _ => printf "it is not a reflexive equality"
  end.

Goal (1 = 1) -> False.
  intros H. is_refl_eq (Constr.type 'H).
Abort.

(** Ltac2 naturally detects when a variable is not used after the matching pattern,
    in which case it triggers a warning.
    This warning will be triggered for non-linear variables, if they are only used
    to constrain the shape of the term matched, like in [is_refl_eq], but no further.
    In this case, the warning can be easily disable by naming unused variables
    starting with [?_] rather than with [?].
    For instance, by matching for [?_x = ?_x] rather than [?x = ?x] in [is_refl_eq].
*)

Ltac2 is_refl_eq' (t : constr) :=
  lazy_match! t with
  | ?_x = ?_x => printf "it is a reflexive equality"
  | _ => printf "it is not a reflexive equality"
  end.

Goal (1 = 1) -> False.
  intros H. is_refl_eq (Constr.type 'H).
Abort.

(** ** 1.3 Matching bound variables

    When a term contains a binder, like [let var := expr in body] or [fun var => body],
    the bound variable [var] only exists inside the binder's scope.
    This raises a difficulty: if we match [let a := ?expr in ?body], then [body]
    is the raw body term, in which [var] appears as a free variable.
    We cannot apply [body] to a different term to substitute for [var], because
    [var] is not a Ltac2 value we can pass around — it is just a name for the binder.

    The solution is to capture the body as a function abstracted over the bound
    variable, using the special pattern [@?body var].
    In a pattern like [let var := ?expr in @?body var]:
    - [?expr] is matched as usual and captures the definition,
    - [var] names the bound variable of the let-in,
    - [@?body var] captures the body as a function: [body] is bound to
      [fun var => <body>], i.e. the body with [var] abstracted out as a lambda.

    After the match, [body] is a [constr] representing a function, and we can
    substitute any term [t] for the former bound variable by applying [$body $t].
    The same pattern works for matching under [fun], [forall], and other binders.

    As a concrete example, let us write a tactic [simplify_let] that takes a
    hypothesis [h] whose type is a let-in [let var := expr in body[var]], and turns
    it into [body[x']], where [x' := expr] is a new shared definition introduced
    in the whole context and goal.

    To do so, we recover the type of [h], and match it against the pattern [let var := ?expr in @?body var].
    After matching, [expr] is the definition and [body] represents [fun var => body].
    We then:
    1. Create a new shared definition [x' := expr] in the whole context and goal
       with [set (x' := $expr) in *].
    2. Retrieve the Ltac2 term for the new hypothesis [x'] with [Control.hyp @x'].
    3. Replace the type of [h] with [$body $x] using [change ($body $x) in h].
      This creates a beta redex that we then reduce with [lazy head beta in h].
*)

Ltac2 simplify_let0 (h : ident) : unit :=
  let type_h := type (Control.hyp h) in
  lazy_match! type_h with
  | let var := ?expr in @?body var =>
      printf "the body is :%t" body;
      set (x' := $expr) in *;
      let x := Control.hyp @x' in
      change ($body $x) in h;
      lazy head beta in h
  | _ => Control.zero (Tactic_failure (Some (fprintf "the type %t of %I is not a letin" type_h h)))
  end.

Ltac2 Notation "simplify_let" h(ident) := simplify_let0 h.

Goal forall x y : nat, (let a := x + 2 in let b := y + 1 in a = b) -> True.
  intros x y h.
  Fail simplify_let x.
  simplify_let h.
Abort.

(** ** 1.4 Using the Unsafe API to Access the Term Structure

    An alternative to [lazy_match!] for inspecting terms is the [Unsafe] submodule
    of [Constr], which exposes the kernel-level representation of terms through the
    function [Unsafe.kind : constr -> kind].
    The type [kind] is an Ltac2 inductive type whose constructors correspond to the
    kernel term formers: [App], [Lambda], [Prod], [LetIn], [Rel], [Var], [Constant], etc.
    The full list is available in the Ltac2 standard library at:
    https://github.com/rocq-prover/rocq/blob/master/theories/Ltac2/Constr.v#L65

    This API is called [Unsafe] because it exposes De Bruijn indices directly.
    In Rocq's kernel, bound variables are represented not by names but by De Bruijn
    indices — natural numbers counting the number of enclosing binders between the
    variable occurrence and the binder that introduced it counting from 1.
    For instance, in [fun x => x], the body [x] is stored as [Rel 1], meaning
    "the variable bound by the immediately enclosing binder".
    If these indices are managed incorrectly — for example by shifting them by the
    wrong amount when going under a binder — the result is a not well-scoped term
    in which an index refers to the wrong binder or to no binder at all, producing
    an ill-scoped term. Hence the [Unsafe] qualifier.

    Because [Unsafe.kind] returns an ordinary Ltac2 value of type [kind], one matches
    on it with a regular Ltac2 [match], not with [lazy_match!], which is specific to
    matching Rocq terms against surface-syntax patterns.

    The main difference with using [lazy_match!] is that:
    1. [lazy_match!] (and its siblings [match!] and [multi_match!]) match
       Rocq terms against patterns. Any number of branches can succeed, or none.
       Moreover, variants of [lazy_match!] discussed in the next section can do
       backtracking to try the next pattern.
    2. A plain Ltac2 [match] is a standard ML-style pattern match on an inductive value:
       only one branch is taken, and no backtracking is involved.
*)

Import Unsafe.

(** In the case of [simplify_let], the main interest of using the [Unsafe] API,
    is that we can directly access the structure of the let in, and do the
    substitution ourselves instead of relying on higher-level tactics like
    [lazy beta iota] which may not always fit perfectly our purpose.

    Here, we can reimplement [simplify_let_bis] by applying [Unsafe.kind] to the
    type of [h] and matching the result against [LetIn _ expr body].
    This gives us [expr] — the bound expression — and [body] — the raw kernel
    term in which the bound variable appears as [Rel 1].
    We then introduce [x' := expr] into the context with [set], recover the
    corresponding hypothesis, and call [substnl [x'] 0 body] to replace every
    occurrence of [Rel 1] in [body] by [x'] in one step, producing [new_body].
    Finally, [change ($new_body) in h] rewrites the type of [h] to [new_body],
    with no intermediate beta redex to reduce.
*)
Ltac2 simplify_let_bis0 (h : ident) : unit :=
  let type_h := type (Control.hyp h) in
  match Unsafe.kind type_h with
  | LetIn _ expr body =>
      set (x' := $expr) in *;
      let x' := Control.hyp @x' in
      let new_body := substnl [x'] 0 body in
      change ($new_body) in h
  | _ => Control.zero (Tactic_failure (Some (fprintf "the type %t of %I is not a letin" type_h h)))

  end.

Ltac2 Notation "simplify_let_bis" h(ident) := simplify_let_bis0 h.

Goal forall x y : nat, (let a := x + 2 in let b := y + 1 in a = b) -> True.
  intros x y h.
  simplify_let_bis h.
Abort.



(** 2. Matching Goals

    2.1 Basics

    Ltac2 also offers the possibility to match the goal to inspect the form of the goal
    to prove, and/or the existence of particular hypotheses like a proof of [False].
    The syntax to match goals is a bit different from matching terms.
    In this case, the patterns are of the form:

        [[ [ x1 : t1, ..., xn : tn |- g ] => ... ]]

    where:
    - [x1] ... [xn] are [ident], i.e. Ltac2 values corresponding to the names
      of the hypotheses. Unlike variables, they should not start with [?].
    - [t1] ... [tn] are the types of the hypotheses, and [g] the type of the goal
      we want to prove. All are of type [constr], the type of Rocq terms in Ltac2.
    - As usual [ident] --- [x1], ..., [xn] --- and any variables that could appear
      in [t1], ..., [tn], and [g], cannot start with an upper case letter as
      it is reserved for constructors.

    Such a pattern will match a goal with conclusion of type [G] where
    [n] different hypotheses of types [T1], ..., [Tn] can be found in the context.
    Each clause must match a different hypothesis for the pattern to succeed.
    Consequently, there must be at least [n] different hypotheses / assumptions
    in the context for such a branch to have a chance to succeed.
    Moreover, the fallback wildcard pattern [_] we used to match terms is
    now [ |- _] as this matches any goals.

    As an example, let us write a small function starting with [lazy_match! goal with]
    to inspect whether the conclusion of the goal is either [_ /\ _] or [_ \/ _].

    As we want to inspect the conclusion of the goal but not the hypotheses,
    our pattern is of the form [ |- g]. To match for [_ /\ _] and [_ \/ _],
    we then get the patterns [ [ |- ?a /\ ?b ] ] and  [ |- ?a \/ ?b ].
*)

Ltac2 and_or_or () :=
  lazy_match! goal with
  | [ |- ?a /\ ?b ] => printf "Goal is %t /\ %t" a b
  | [ |- ?a \/ ?b ] => printf "Goal is %t \/ %t" a b
  | [ |- _] => Control.zero (Tactic_failure (Some (fprintf
                "The goal is not a conjunction nor a disjunction")))
  end.

Goal True /\ False.
  and_or_or ().
Abort.

Goal False \/ True.
  and_or_or ().
Abort.

Goal nat.
  Fail and_or_or ().
Abort.

(** To match for an hypothesis of type [nat] but not to check anything on the goal,
    we would use the pattern [n : nat |- _] as below. To match for a pair of
    hypotheses [nat], we would then use the pattern [n : nat, m : nat |- _].
*)

Goal forall (n : nat) (b : bool) (m : nat), True.
  intros n b m.
  lazy_match! goal with
  | [n : nat |- _] => printf "succeeded, hypothesis %I" n
  end.
Abort.

Goal nat -> bool -> nat -> True.
  intros n b m.
  lazy_match! goal with
  | [n1 : nat, n2 : nat |- _] => printf "succeeded, hypothesis %I %I" n1 n2
  | [ |- _ ] => fail
  end.
Abort.

(** We can see, we do need at least an hypothesis per pattern. If we remove
    [m : nat] this will now fail.
*)
Goal forall (n : nat) (b : bool), True.
  intros n b.
  Fail lazy_match! goal with
  | [n1 : nat, n2 : nat |- _] => printf "succeeded, hypothesis %I %I" n1 n2
  end.
Abort.

(** By default the hypotheses are matched from the last one to the first one.
    This can be seen in the example above as it prints [m], the last variable
    of type [nat] that was introduced.
    We can start from the first one, by matching [reverse goal] rather than [goal].
    For instance, in the example below, [m] is found if we match the goal for
    [ [h : nat |- _] ] as it is the last hypothesis of type [nat] that was
    introduced. However, it is [n] that is found if match [reverse goal] as it
    is the first hypothesis of type [nat] that was introduced.
*)

Goal forall (n : nat) (b : bool) (m : nat), True.
  intros n b m.
  lazy_match! reverse goal with
  | [n : nat |- _] => printf "succeeded, hypothesis %I" n
  | [ |- _ ] => fail
  end.
Abort.

(** There must be exactly one goal under focus for it to be possible to match
    the goal, as otherwise the notion of "the goal" would not have much meaning.
    If more than one goal is focus, it will hence fail with the error [Not_focussed].
*)

Goal False /\ True.
  split.
  Fail
  (* all focuses on two goals [False] and [True] *)
  all: lazy_match! goal with
  | [ |- _] => ()
  end.
Abort.

(** Consequently if you want to match the goals, be sure to focus a single goal first,
    for instance with [Control.enter : (unit -> unit) -> unit] that applies a
    tactic [tac : unit -> unit] independently to each goal under focus.
*)

(* 2.2 Non-Linear Matching *)

(** As for matching terms, matching goals is by default syntactic.
    However, matching for non-linear variables is a bit more involved.
    In the non-linear case, variables are matched up to conversion when they appear
    in different clauses, and up to syntax when they appear in the same clause.

    To understand this better, let us look at an example.
    We could write a version of [eassumption] by matching for the pattern [_ : ?t |- ?t].
    In this case, as [?t] appears in different clauses, one of hypotheses and
    in the conclusion, it will hence be matched up to conversion.
    We can check it works by supposing [0 + 1 = 0] and trying to prove [1 = 0],
    as [0 + 1] is equal to [1] up to conversion but not syntactically.
*)

Goal 0 + 1 = 0 -> 1 = 0.
  intros.
  lazy_match! goal with
  | [ _ : ?t |- ?t] => printf "succeeded: %t" t
  | [ |- _ ] => fail
  end.
Abort.

(** However, if a variable appears several times in a same clause, then it is
    compared syntactically. For instance, in [ |- ?t = ?t], [?t] is compared
    syntactically as it appears twice in the goal which forms one clause.
*)

Goal 1 + 1 = 2.
  Fail lazy_match! goal with
  | [ |- ?t = ?t] => printf "equality is %t" t
  | [ |- _ ] => fail
  end.
Abort.

(** A subtlety to understand is that only the hole associated to a variable will
    be compared up to conversion, other symbols are matched syntactically as usual.
    For instance, if we match for [?t, ~(?t)], the symbol [~] will matched,
    if one is found, then inside the clause ~(X) it will be compared
    up to conversion with [?t].

    Consequently, if we have [P], it will fail to match for [P -> False] as
    [~] is matched syntactically, but [P -> False] is the unfolding of [~P].
*)

Goal forall P, P -> (P -> False) -> False.
  intros.
  Fail match! goal with
  | [_ : ?t, _ : ~(?t) |- _ ] => printf "succeed: %t" t
  | [ |- _ ] => fail
  end.
Abort.

(** However, matching for [~((fun _ => P) 0)] will work as [~] will be matched,
    then [(fun _ => P)0] matched with [P] up to conversion which works.
*)

Goal forall P, P -> ~((fun _ => P) 0) -> False.
  intros.
  match! goal with
  | [_ : ?t, _ : ~(?t) |- _ ] => printf "succeed: %t" t
  | [ |- _ ] => fail
  end.
Abort.

(** It often happens that non-linear matching is not precise enough for our
    purpose, either because we would like to match both terms in one clause
    up to conversion, or because we would like to use a different notion of
    equality for non-linear occurrences, like syntactic equality, equality up to
    some reduction, or even up to unification.

    In this case, the best approach is to use different variables for each
    occurrence we want to compare, then call the comparison we wish.
    For instance, to match for [P] and [~P] up to unification, we would:
    match for a pair of variables [t1], [t2] then call a unification function
    to check if one of the hypotheses is indeed a negation of the other.
*)

Goal forall P, P -> (P -> False) -> False.
  intros.
  match! goal with
  | [ _ : ?t1, _ : ?t2 |- _] =>
      Unification.unify_with_full_ts t2 '($t1 -> False);
      printf "success"
  | [ |- _ ] => fail
  end.
Abort.

(** The advantage of this method is that it provides the user with fine-grained
    control over when and how reduction and equality tests are performed.
*)

(* 3. Backtracking and [lazy_match!], [match!], [multi_match!] *)

(** 3.1 [lazy_match!]

    [lazy_match!] is the easiest command to understand and to use.
    [lazy_match!] picks a branch, and sticks to it even if the code executed
    after picking this branch (the body of the branch) leads to a failure.
    It will not backtrack to pick another branch if a choice leads to a failure.

    For instance, in the example below, it picks the first branch as everything
    matches [[ |- _]]. It prints "branch 1", then fails. As no backtracking is
    allowed, it sticks to this choice and fails.
*)

Goal False.
  Fail lazy_match! goal with
  | [ |- _ ] => printf "branch 1"; fail
  | [ |- _ ] => printf "branch 2"
  | [ |- _ ] => printf "branch 3"
  end.
Abort.

(** [lazy_match!] should be considered as the default, as it is easy to understand
    (no backtracking) which prevents unexpected behaviour, and yet sufficient
    for all applications where matching the syntax is sufficient to decide what to do.

    A common use of [lazy_match!] is to make a decision based on the shape of the
    goal or the shape of a term or type.

    As a simple example, let us write a tactic [split_and] that introduces
    variables and hypotheses with [intros ?] if the goal is of the form [A -> B],
    splits the goal with [split] if it is a conjunction [A /\ B], and recursively
    simplify the new goals.
    In both cases, the syntactic equality test is sufficient to decide what to do
    as if it is of the required form, then the branch will succeed.
    One should hence use [lazy_match!], which leads to the following simple function:
*)

Ltac2 rec split_and () :=
  lazy_match! goal with
  | [ |- _ -> _ ] => intros ?; split_and ()
  | [ |- _ /\ _ ] => split > [split_and () | split_and ()]
  | [ |- _ ] => ()
  end.

Goal (True /\ ((False /\ True) /\ False)) /\ True.
  split_and ().
Abort.

Goal forall (n : nat), (forall m, m = n) /\ (False \/ False) /\ True.
  split_and ().
Abort.

Goal True \/ False.
  Fail (progress (split_and ())).
Abort.
(** 3.2 [match!]

      [match! goal with] picks the first branch that matches.
      Then, if evaluation of its body fails, it backtracks
      and picks the next matching pattern,
      potentially the same one if all the hypotheses have not been exhausted yet.

      In the example below the first branch is picked and fails, it hence
      backtracks to its choice.
      There is only one possibility for the pattern [ |- _] as it matches any goal.
      As it has already been tried, it hence switches to the second pattern which is [ |- _].
      This branch now succeeds, hence the whole [match!].
*)

Goal False.
  match! goal with
  | [ |- _ ] => printf "branch 1"; fail
  | [ |- _ ] => printf "branch 2"
  | [ |- _ ] => printf "branch 3"
  end.
Abort.
(** [match!] is useful as soon as matching the syntax is not enough, and we
    need additional tests to see if we have picked the right branch or not.
    Indeed, if such a test fails raising an exception (or we make it so), then
    [match!] will backtrack, and look for the next branch matching the pattern.

    A common application of [match!] is to match the goal for hypotheses, then
    do extra tests to decide what to do, or ensure we have picked the right ones.
    If we have not, failing triggers backtracking to the next candidate hypothesis.

    A basic example is to recode a simple [eassumption] tactic, that tries
    to solve the goal with [exact P] for all hypotheses [P].
    If we match the goal with the pattern [p : _ |- _] to get a [P], it is most
    likely the first hypothesis [P] picked will not solve the goal, and hence
    that [exact P] will fail.
    In this case, we want to backtrack to try the next hypothesis [P].

    It is only if [exact P] succeeds that we know we have picked the good branch.
    Consequently, we want to use [match!] and not [lazy_match!].
*)

Ltac2 my_eassumption () :=
  match! goal with
  | [p : _ |- _] =>
      printf "Try %I" p;
      let p := Control.hyp p in exact $p
  | [ |- _] => Control.zero (Tactic_failure (Some (fprintf "No such assumption")))
  end.

Goal forall P Q, P -> Q -> P.
  intros P Q p q. my_eassumption ().
Qed.

Goal forall P Q, P -> P -> Q.
  intros P Q p1 p2. Fail my_eassumption ().
Abort.
(** 3.3 [multi_match!]

      [multi_match! goal with] is more complex and subtle. It basically behaves
      like [match!] except that it will further backtrack if the choice of a
      branch leads to a subsequent failure when linked with another tactic.

      For instance, in the example below we link the [match!] with [fail], to make
      the composition fail. In the [match!] case, it will try the first branch,
      then the second that succeeds, then try [fail], and hence fail.
      It will hence print [branch 1] and [branch 2], and then fail.
*)

Goal False.
  Fail match! goal with
  | [ |- _ ] => printf "branch 1"; fail
  | [ |- _ ] => printf "branch 2"
  | [ |- _ ] => printf "branch 3"
  end; fail.
Abort.

(** In contrast, when the composition fails [multi_match!] will further backtrack
    to its choice of branch, in this case the second one, and try the next matching branch.
    The idea is that picking a different branch could have led to the subsequent
    tactic to succeed, as it can happen when using [constructor].
    Here, as [fail] always fails, it will still failed but we can see it did
    backtrack and tried the third branch as it will print [branch 3].
*)

Goal False.
  Fail multi_match! goal with
  | [ |- _ ] => printf "branch 1"; fail
  | [ |- _ ] => printf "branch 2"
  | [ |- _ ] => printf "branch 3"
  end; fail.
Abort.

(** [multi_match!] is meant to write tactics performing a choice, and that
    we want to link with other tactics, like the [constructor] tactic
    that we can then link with [reflexivity] or [assumption] to solve the goal.

    A basic example is to code a tactic that recursively picks [left] or [right]
    if the goal is for the form [A \/ B], which is similar to [repeat constructor].
    The choices [left] or [right] are both correct as soon as the goal is of the
    form [A \/ B]. We can only know if we have picked the good one, once chained
    with another tactic that tries to solve the goal.
    We hence need to use [multi_match!] as if we have picked the wrong side
    to prove, we want to backtrack to pick the other side.

    This leads to the following small script, improved with printing to display
    the backtracking structure:

*)

Ltac2 rec left_or_right () :=
  multi_match! goal with
  | [ |- _ \/ _ ] => print_goals; printf "use left"; left; left_or_right ()
  | [ |- _ \/ _ ] => print_goals; printf "use right"; right; left_or_right ()
  | [ |- ?t ] => printf "the final goal is %t" t ; printf "-------"
  end.

Goal False \/ (False \/ True) \/ 0 = 1.
  left_or_right (); exact I.
Abort.

Goal False \/ (False \/ False) \/ (0 = 1 -> 0 = 1).
  left_or_right (); intros X; exact X.
Abort.

(** [multi_match!] is **not meant** to be used by default.
    Yes, it is the more powerful match primitive in terms of backtracking, but it
    can be hard to understand, predict and debug, in particular for newcomers.
    Moreover, it can be expensive as it can perform an exponential number of
    backtracking attempts when linked with another tactic that can backtrack.
    It should hence only be used when needed.
*)
