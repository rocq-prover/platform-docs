(** * Tutorial Ltac2 : Ltac2 for Ltac1 Users

    *** Main contributors
    - Thomas Lamiaux

    *** Summary

    Ltac2 is the successor of Ltac1, and is designed to replace Ltac1 as the
    standard tactic language for the Rocq proof assistant.

    This tutorial is meant to introduce Ltac2 for users that already are
    familiar with Ltac1. We mainly focus on the differences with Ltac1, and how
    to translate your existing Ltac1 knowledge into Ltac2 idioms.

    *** Table of content

    - 1. Introduction
      - 1.1 A Brief History of Ltac1
      - 1.2 Design Flaws of Ltac1
      - 1.3 Ltac2
      - 1.4 Status of Ltac2
    - 2. Using Ltac2 to Write Proofs
      - 2.1 Basic Syntax Changes
      - 2.2 Interoperability Between Ltac1 and Ltac2
      - 2.3 Some Notations Are Missing
    - 3. Ltac2 is a Proper Functional Programming Language
      - 3.1 Types and Type Inference
      - 3.2 Call-by-Value Semantics and Thunking
      - 3.3 Effects: Printf and References
    - 4. Ltac2 as a Meta-Programming Language for Rocq
      - 4.1 Foreign Function Interface
      - 4.2 Quoting and Unquoting
      - 4.3 Matching Terms and Goals
      - 4.4 Backtracking
      - 4.5 Notations

    *** Prerequisites

    Needed:
    - Familiarity with Ltac1 and basic Rocq proof writing.

    Installation:
    - Ltac2 and its core library are available by default with Rocq.

*)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Printf.


(** ** 1. Introduction

    *** 1.1 A Brief History of Ltac1

    Ltac1 was introduce in 2000 (Coq 7.0) to enable users to write their own
    tactics by combining existing primitive tactics using an expressive set of
    combinators.

    For instance, users have been using Ltac1 to write variants of existing
    tactics domain specific automation tactic.

    Ltac1 was key in the success of Rocq, and of many formalization efforts as
    it enabled us to write proofs in a more incremental, efficient and more
    robust way than the state of the art of that time.


    *** 1.2 Design Flaws of Ltac1

    Yet, Ltac1 was not planned for so advanced uses and suffer designed flaws.

    1. At the time, there were no idea of what a good tactic language ought to be
       and Ltac1 was not designed following current PL conventions

    2. The development of Ltac1 was not carefully planned, and features have
       added piecewise over times by different contributors.
       Consequently, the language is far from well-designed, uniform, or well
       implemented, making improvements and every day use complicated.

    3. Ltac1 tried to accomodate two contradictory feature: for tactics
       to be both automagical and predictible.
       To do so, Ltac1 implements many dynamic decision procedures to facilitates
       writing tactics that works well for small example but do not scale well.

    With experirence, there are several well-known design flaws with Ltac1:

    - **No type system.** Ltac1 is completely untyped. Any value can be passed to
      any function, and type errors are only caught at runtime, often with cryptic
      error messages. This makes writing large library and tactics and debugging
      very tedious.

    - **No data structures.** Ltac1 has no lists, no records, and no algebraic
      types. All state must be threaded through the goal or through side channels.

    - **Unclear Semantic** It is hard to predict when a tactic will be
      evaluated, or whether a name refers to a Rocq term or an Ltac1 variable.
      This leads to subtle and hard-to-diagnose bugs.

    - **Limited effects.** Ltac1 lacks support for many basic effects that
      are useful in a programming language like printing, or mutable references.

    - **Implicit quoting.** The boundary between Gallina (Rocq terms) and Ltac1
      meta-programs is not syntactically marked. Ltac1 uses dynamic scoping rules
      to resolve names, which are hard to understand and debug.

    - **Poor FFI.** Functions from the Rocq kernel are imported all at once,
      without types and without any control over what is in scope.


    *** 1.3 Ltac2

    Ltac2 is designed to be the replacement of Ltac1, and offer both a
    reliable and scalable tactic language for Rocq, while being as backward
    compatible as possible.

    Its core improvements over Ltac1 are:

    - It is a proper typed functional programming language of the Hindley–Milner
      family, similarly to OCaml, with type inference, algebraic data types,
      and a clear call-by-value semantic.

    - It has an explicit typed Foreign Function Interface.
      This makes it easy to extend Ltac2 to expose and access primitive like unification,
      that were not accessible before, while providing better documentation for it.
      As a consequence, it is possible to do more stuff in Ltac2 than in Ltac1.
      For instance, it is now possible to manipulate to goal state, and modify
      the set of goals under focus etc.

    - Quoting and unquoting between Rocq terms (Gallina) and Ltac2 values is now
      explicit and syntactically marked. It no longer relies on a hard to predict
      dynamic decision procedure.

    - Backtracking is modelled as streams of possibilities, with fine-grained
      primitives to manipulate it.

    *** 1.4 Status of Ltac2

    Ltac2 is actively developed and included in every Rocq distribution.
    No extra package is needed. Ltac2 may still contain bugs or limitations,
    but it is already more reliable and expressive than Ltac1.

    Therefore, while Ltac1 is not going away anytime soon, we would like to
    strongly encourage users to use Ltac2 (or other alternatives) instead of Ltac1
    for new projects and new automation code in existing projects.

    It comes with a CoreLibrary that is meant to contain basic building blocks
    for creating complex tactics. It keeps evolving and may contain more
    exposed primitives in more recent versions of Rocq.
    See https://github.com/rocq-prover/rocq/tree/master/theories/Ltac2 for
    the master branch of Rocq.

*)


(** ** 2. Using Ltac2 to Write Proofs *)

(** *** 2.1 Basic Syntax Changes

    The first thing you will notice when moving from Ltac1 to Ltac2 is that the
    declaration syntax has changed.

    In Ltac1, a tactic is defined as:
<<
    Ltac my_tac := tac1; tac2.
>>
    In Ltac2, the syntax becomes:
<<
    Ltac2 my_tac () := tac1; tac2.
>>
    The extra [()] parameter, of type [unit], is required because Ltac2 is a
    strict call-by-value language (see Section 3.2 for the details).
    Without it, the body would be evaluated immediately at definition time rather
    than when the tactic is called.

    Semicolon chaining [;] works exactly as in Ltac1: [tac1; tac2] applies [tac2]
    to all goals generated by [tac1].
    Standard tactics ([intros], [destruct], [rewrite], [apply], [exact], etc.)
    are available with the same names.

    Here is the same simple tactic written in both languages:
*)

(* Ltac1:
   Ltac my_split_exact := split; exact I. *)

Ltac2 my_split_exact0 () := split; exact I.

Goal True /\ True.
  my_split_exact0 ().
Qed.

(** Writing [()] at every call site is noisy.
    The standard idiom is to declare a [Ltac2 Notation] — here a simple
    abbreviation — that inserts the [()] application automatically.
*)

Ltac2 Notation my_split_exact := my_split_exact0 ().

Goal True /\ True.
  my_split_exact.
Qed.


(** *** 2.2 Interoperability Between Ltac1 and Ltac2

    You do not have to rewrite everything at once.
    Ltac1 and Ltac2 can freely call each other, which makes incremental migration
    practical.

    **** 2.2.1 Calling Ltac2 from Ltac1

    To embed a Ltac2 tactic inside an Ltac1 proof script, use [ltac2:(...)].
    The Ltac2 expression inside must have type [unit].
    This is the most common migration pattern: keep existing proof scripts in
    Ltac1 while writing new automation in Ltac2.

    For instance, the following Ltac1 tactic delegates entirely to a Ltac2
    definition.  It can be called in any Ltac1 proof script:
<<
    Ltac use_ltac2_in_ltac1 := ltac2:(greet_and_close ()).
    Goal True. use_ltac2_in_ltac1. Qed.
>>
*)

Ltac2 greet_and_close () :=
  printf "closing goal with exact I";
  exact I.

(** We can verify the Ltac2 function itself works in a Ltac2 proof: *)

Goal True.
  greet_and_close ().
Qed.

(** **** 2.2.2 Calling Ltac1 from Ltac2

    Symmetrically, a Ltac2 definition can invoke Ltac1 code using [ltac1:(...)].
    This is useful to reuse existing Ltac1 automation that you have not yet ported.
*)

Ltac2 use_auto () := ltac1:(auto).

Goal 0 = 0.
  use_auto ().
Qed.

(** **** 2.2.3 The "Classical" Migration Pattern

    A natural approach when migrating a large development is:
    1. Write new automation helpers in Ltac2.
    2. Bridge them into Ltac1 via [ltac2:(...)].
    3. Use them in existing proof scripts without further changes.

    This lets you enjoy Ltac2's type safety and expressiveness in new code while
    leaving all existing proofs untouched.
    For example, suppose you want to port an Ltac1 assumption-solver to Ltac2.
    You can define it in Ltac2 and expose it as an Ltac1 tactic via [ltac2:(...)]:
*)

Ltac2 my_exact_assumption0 () :=
  match! goal with
  | [h : ?t |- ?g] =>
      if Constr.equal t g
      then let term := Control.hyp h in exact $term
      else Control.zero (Tactic_failure None)
  end.

(** The bridge for existing Ltac1 proof scripts looks like:
<<
    Ltac my_exact_assumption := ltac2:(my_exact_assumption0 ()).
    Goal nat -> nat. intros n. my_exact_assumption. Qed.
>>

    In the rest of this tutorial we work directly in Ltac2, so we define a
    notation instead:
*)


(** *** 2.3 Some Notations Are Missing

    Not all Ltac1 shorthand is available in Ltac2 by default.
    In particular, several tactics that accept inline introduction patterns
    — such as [intros [H1 H2]] or [induction n as [|n' IH]] — require the
    extra [Ltac2.Notations] module in Ltac2.

    Importing [Ltac2.Notations] recovers most of them:
*)

From Ltac2 Require Import Notations.

Goal forall n : nat, n + 0 = n.
  intro n. induction n as [|n' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.


(** ** 3. Ltac2 is a Proper Functional Programming Language *)

(** *** 3.1 Types and Type Inference

    The most fundamental difference between Ltac1 and Ltac2 is that Ltac2 is a
    statically typed language with Hindley–Milner type inference, very similar
    to OCaml.

    In Ltac1 there is no type system: values are opaque and type errors are only
    caught at runtime with cryptic messages.
    In Ltac2, every expression has a type, and ill-typed programs are rejected
    before they are run.
    Type annotations are optional — the type checker infers them — but can be
    written for documentation or disambiguation.

    As in OCaml, constructor names must start with an **uppercase** letter
    ([Some], [None], [S], [O], …), while variable and function names must start
    with a **lowercase** letter.

    Here is a simple typed function:
*)

Ltac2 add (x : int) (y : int) : int := Int.add x y.
Ltac2 Eval add 2 3.

(** Ltac2 supports Hindley–Milner polymorphism.
    The following identity function works at any type:
*)

Ltac2 my_id (x : 'a) : 'a := x.
Ltac2 Eval my_id 42.
Ltac2 Eval my_id true.

(** Ltac2 provides standard data structures: lists, options, pairs, etc.
    These are available from the Ltac2 standard library after the base import.
    For example, here are a list computation and a polymorphic function over
    options:
*)

Ltac2 Eval List.map (fun x => Int.add x 1) [1; 2; 3].

Ltac2 safe_head (l : 'a list) : 'a option :=
  match l with
  | [] => None
  | h :: _ => Some h
  end.

Ltac2 Eval safe_head [1; 2; 3].
Ltac2 Eval safe_head ([] : int list).


(** *** 3.2 Call-by-Value Semantics and Thunking

    Ltac1 has an unclear, hard-to-predict evaluation order.
    Ltac2 is strictly **call-by-value**: function arguments are fully evaluated
    before the function body is entered.
    This makes behavior predictable and intuitive, but it has one important
    consequence for passing tactics as arguments.

    If you pass a tactic [t] as an argument to a function, [t] is evaluated
    — i.e. executed — immediately, before the body of the function has a chance
    to decide whether to use it.
    To illustrate, consider a function that ignores its argument and does nothing:
*)

Ltac2 bad_ignore (_ : unit) : unit := ().

(** Passing [fail] to [bad_ignore] causes the whole call to fail, because
    [fail] is evaluated before [bad_ignore] is entered:
*)

Goal True.
  Fail bad_ignore fail.
Abort.

(** The fix is to **thunk** the argument: wrap the tactic in [fun () => ...].
    A thunk is only evaluated when applied to [()], so the callee can decide
    when (or whether) to run it.
*)

Ltac2 good_ignore0 (_ : unit -> unit) : unit := ().

Goal True.
  good_ignore0 (fun () => fail).
  exact I.
Qed.

(** Writing [fun () => ...] at every call site is noisy.
    A [Ltac2 Notation] with the [thunk(tactic)] parser inserts thunks automatically,
    hiding this detail from callers.

    For simple abbreviations (no extra parsing), it suffices to declare a notation
    that applies the thunked function:
*)

Ltac2 Notation good_ignore := good_ignore0.

Goal True.
  good_ignore fail.
  exact I.
Qed.

(** For more details on thunking and the type of tactics, see
    [tutorial_types_and_thunking.v] in this folder.
*)


(** *** 3.3 Effects: Printf and References

    In Ltac1, [idtac] is the only way to print, and there is no mutable state.
    Ltac2 has a proper typed [printf] and ML-style mutable references.

    **** 3.3.1 Printf

    [printf] takes a format string with typed specifiers:
    - [%t] formats a [constr] (a Rocq term)
    - [%I] formats an [ident] (a hypothesis or variable name)
    - [%s] formats a [string]

    This makes it much easier to inspect the proof state or debug automation
    than the [idtac] approach:
*)

Goal nat -> bool -> True.
  intros n b.
  printf "n has type %t" (Constr.type (Control.hyp @n));
  printf "b has type %t" (Constr.type (Control.hyp @b)).
  exact I.
Qed.

(** **** 3.3.2 Mutable References

    Ltac2 provides ML-style mutable references of type ['a ref], with a
    mutable [contents] field.
    They can be used to accumulate state across multiple tactic calls — something
    that is impossible in Ltac1.

    A reference is created as a record literal [{ contents := initial_value }],
    its current value is read with [r.(contents)], and it is mutated with
    the setter [Ref.set r new_value].
    See the Ltac2 core library for the full [Ref] module API:
    https://github.com/rocq-prover/rocq/blob/master/theories/Ltac2/Ref.v
*)


(** ** 4. Ltac2 as a Meta-Programming Language for Rocq *)

(** *** 4.1 Foreign Function Interface

    In Ltac1, all interaction with the Rocq kernel happens through built-in
    tactics imported as a single opaque block — no types, no control over what
    is in scope.

    Ltac2 has an explicit, typed Foreign Function Interface (FFI).
    Kernel functions are exposed in a hierarchy of typed modules:
    - [Constr]: inspect, build, and compare Rocq terms
    - [Std]: reduce terms, call unification, access the environment
    - [Unsafe]: access the raw kernel representation of terms
    - [Ind]: inspect inductive types and their constructors
    - [Control]: interact with the proof state and backtracking

    The full core library is at:
    https://github.com/rocq-prover/rocq/tree/master/theories/Ltac2

    For example, [Constr.type] retrieves the type of a term and [Std.eval_hnf]
    reduces it to head-normal form:
*)

Ltac2 print_type (t : constr) : unit :=
  printf "%t : %t" t (Constr.type t).

Ltac2 print_hnf_type (t : constr) : unit :=
  print_type (Std.eval_hnf t).

Goal True.
  print_hnf_type '(1 + 1).
  exact I.
Qed.


(** *** 4.2 Quoting and Unquoting

    One of the main sources of confusion in Ltac1 is the implicit boundary
    between Gallina (the language of Rocq terms) and Ltac1 meta-programs.
    Ltac1 uses dynamic scoping rules to resolve names, leading to subtle bugs
    when a name is mistaken for a Rocq term instead of an Ltac1 variable, or
    vice versa.

    Ltac2 makes this boundary **explicit** through quoting and unquoting operators.

    **** 4.2.1 Quoting Rocq Terms

    To embed a Rocq term into Ltac2 as a value of type [constr], use ['] (apostrophe).
    In Ltac1, terms in patterns were implicitly quoted; there was no explicit notation:
*)

(* Ltac1:
   Ltac use_T :=
     match goal with
     | _ : T |- _ => assumption  (* T is implicitly a Rocq term *)
     end. *)

Ltac2 Eval 'nat.
Ltac2 Eval '(0 = 0).
Ltac2 Eval '(forall n : nat, n + 0 = n).

(** **** 4.2.2 Unquoting

    To use a Ltac2 [constr] value back in a tactic position, unquote it with
    [$] (dollar sign):
*)

Goal True /\ True.
  let t := 'I in
  split; exact $t; exact $t.
Qed.

(** **** 4.2.3 Identifiers and References

    To create an [ident] value (the name of a hypothesis or variable), use
    [@name] syntax.
    To recover the corresponding term from a hypothesis name, use [Control.hyp]:
*)

Goal nat -> 0 = 0.
  intros H.
  printf "H : %t" (Constr.type (Control.hyp @H)).
  reflexivity.
Qed.

(** [reference:(name)] creates a [Std.reference] pointing to a global constant.
    Pass it to [Env.instantiate] to recover the corresponding Rocq term:
*)

Ltac2 Eval Env.instantiate reference:(nat).

(** For a complete treatment of quoting, see [tutorial_quoting.v] in this folder. *)


(** *** 4.3 Matching Terms and Goals

    Ltac1 provides [match goal] and [lazymatch goal] for pattern-matching the
    proof state.
    Ltac2 provides three matching combinators:

    - [lazy_match! goal] — like Ltac1 [lazymatch goal]: tries patterns in order,
      does **not** backtrack into a branch once a pattern has matched.
    - [match! goal] — like Ltac1 [match goal]: tries patterns in order, and
      **does** backtrack into a branch if it raises an exception.
    - [multi_match! goal] — backtracks both into branches and into patterns.

    The key syntactic differences from Ltac1:
    - Write [lazy_match! goal with] instead of [lazymatch goal with]
    - Hypothesis bindings [h : ?t] produce [h : ident] (the name) and
      [t : constr] (the type). To recover the corresponding term, use
      [Control.hyp h].

    Here is a direct comparison.

    In Ltac1:
<<
    Ltac show_hyp_type :=
      lazymatch goal with
      | H : ?T |- _ => idtac T
      end.
>>
    In Ltac2:
*)

Ltac2 show_hyp_type0 () :=
  lazy_match! goal with
  | [_h : ?t |- _] => printf "a hypothesis has type %t" t
  end.

Ltac2 Notation show_hyp_type := show_hyp_type0 ().

Goal nat -> True.
  intros H.
  show_hyp_type.
  exact I.
Qed.

(** With [match!], the match backtracks into the branch if it fails, which allows
    trying every matching hypothesis in turn.
    For example, here is a reimplementation of [assumption] that iterates over
    all hypotheses, trying [exact] on each one, until one succeeds:
*)

Ltac2 my_assumption0 () :=
  match! goal with
  | [h : _ |- _] => let term := Control.hyp h in exact $term
  end.

Ltac2 Notation my_assumption := my_assumption0 ().

Goal nat -> nat.
  intros n. my_assumption.
Qed.

(** If the goal type does not match any hypothesis, [exact $term] fails for
    every candidate, and the whole [match!] ultimately raises an exception:
*)

Goal nat -> bool -> nat.
  intros n b. my_assumption.
Qed.

(** For a deeper treatment of matching, see [tutorial_matching_terms_and_goals.v]. *)


(** *** 4.4 Backtracking

    Ltac1 controls backtracking through:
    - [match goal] (backtracks into branches on failure),
    - [fail n] (propagates failure [n] levels up through [match] branches),
    - [first [tac1 | tac2 | ...]] (tries alternatives in order).

    Ltac2 models backtracking as **streams of possibilities** and exposes three
    explicit low-level primitives:

    - [Control.zero : exn -> 'a] — raises an exception and triggers backtracking.
      This is the primitive underlying Ltac2 [fail].
    - [Control.plus : (unit -> 'a) -> (exn -> 'a) -> 'a] — stacks a backtracking
      choice: try the first thunk; on exception, try the handler.
      This is the primitive underlying [tac1 + tac2].
    - [Control.case : (unit -> 'a) -> ('a * (exn -> 'a)) result] — inspects
      whether a tactic has at least one success without consuming it.

    Note that in Ltac2, [fail] is defined as
    [Control.enter (fun () => Control.zero (Tactic_failure None))],
    making its meaning precise.

    Regarding [fail n]: Ltac1's [fail n] propagates failure through [n] levels of
    [match] branches. This is not needed in Ltac2 because backtracking always
    propagates unless explicitly stopped via [Control.throw] (a non-backtrackable
    exception).

    Here is a reimplementation of [first] using [Control.plus]:
*)

Ltac2 rec my_first (tacs : (unit -> unit) list) : unit :=
  match tacs with
  | [] =>
      Control.zero (Tactic_failure (Some (fprintf "my_first: all tactics failed")))
  | t :: rest =>
      Control.plus t (fun _ => my_first rest)
  end.

Ltac2 always_fail () : unit :=
  Control.zero (Tactic_failure (Some (fprintf "always_fail"))).

Goal 0 = 0.
  my_first [always_fail; always_fail; fun () => reflexivity].
Qed.

Goal 0 = 0.
  Fail my_first [always_fail; always_fail].
Abort.

(** For a detailed treatment of backtracking and its primitives, see
    [tutorial_backtracking.v] in this folder.
*)


(** *** 4.5 Notations

    Ltac1 defines tactic notations using [Tactic Notation]:
<<
    Tactic Notation "my_or" tactic(t1) "or" tactic(t2) :=
      first [t1 | t2].
>>
    Ltac2 has [Ltac2 Notation] with explicit argument parsers.
    The crucial difference is that tactic arguments should be declared with
    [thunk(tactic)] to avoid premature evaluation (see Section 3.2).

    The available argument parsers include:
    - [tactic] — parse a tactic (evaluated eagerly; use [thunk] for tactics)
    - [thunk(tactic)] — parse a tactic, wrap it in [fun () => ...]
    - [ident] — parse an identifier
    - [constr] — parse a Rocq term

    For infix notations, the separator keyword must not be a Rocq built-in, and
    arguments must be delimited to avoid ambiguous greedy parsing.
    A safe pattern is to use brackets, following the convention of the built-in
    [first [tac1 | tac2]] notation:
*)

Ltac2 my_or0 (t1 : unit -> unit) (t2 : unit -> unit) : unit :=
  Control.plus t1 (fun _ => t2 ()).

Ltac2 Notation "my_or" "[" t1(thunk(tactic)) "|" t2(thunk(tactic)) "]" :=
  my_or0 t1 t2.

Goal True.
  my_or [ exact I | fail ].
Qed.

Goal True.
  my_or [ fail | exact I ].
Qed.

(** For simple aliases with no extra parsing, use an abbreviation notation that
    just expands to a Ltac2 expression:
*)

Ltac2 Notation my_exact_assumption := my_exact_assumption0 ().

Goal nat -> nat.
  intros n. my_exact_assumption.
Qed.
