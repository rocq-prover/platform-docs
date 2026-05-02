(** * Tutorial Ltac2 : Ltac2 for Ltac1 Users

    *** Main contributors
    - Thomas Lamiaux

    *** Summary

    Ltac2 is the successor of Ltac1, and is designed to replace Ltac1 as the
    standard tactic language for the Rocq proof assistant.

    This tutorial is meant to introduce Ltac2 for users that already are
    familiar with Ltac1. We mainly focus on the differences with Ltac1, and how
    to translate your existing Ltac1 knowledge into Ltac2 idioms.

    *** Table of contents

    - 1. Introduction
      - 1.1 A Brief History of Ltac1
      - 1.2 Design Flaws of Ltac1
      - 1.3 Ltac2
      - 1.4 Status of Ltac2
    - 2. Using Ltac2 to Write Proofs
      - 2.1 Using Ltac2 in the Ltac1 Proof Mode
      - 2.2 Using the Ltac2 Proof Mode
    - 3. Ltac2 Is a Proper Functional Programming Language
      - 3.1 Types and Type Inference
      - 3.2 Call-by-Value Semantics and Thunking
      - 3.3 Effects: Printf and References
      - 3.4 Exceptions
    - 4. Ltac2 as a Meta-Programming Language for Rocq
      - 4.1 Foreign Function Interface
      - 4.2 Matching Terms and Goals
      - 4.3 Quoting and Unquoting
      - 4.4 Backtracking
      - 4.5 Notations
    - 5. Small Case Study

    *** Prerequisites

    Needed:
    - Familiarity with Ltac1 and basic Rocq proof writing.

    Installation:
    - Ltac2 and its core library are available by default with Rocq.

*)


(** ** 1. Introduction

    *** 1.1 A Brief History of Ltac1

    Ltac1 was introduced in 2000 (Coq 7.0) to enable users to write their own
    tactics by combining existing primitive tactics using an expressive set of
    combinators.

    For instance, users have been using Ltac1 to write variants of existing
    tactics or domain-specific automation tactics.

    Ltac1 was key in the success of Rocq, and of many formalization efforts as
    it enabled us to write proofs in a more incremental, efficient and more
    robust way than the state of the art of that time.


    *** 1.2 Design Flaws of Ltac1

    Yet, Ltac1 was not planned for such advanced uses and suffered from design flaws.

    1. At the time, there was no idea of what a good tactic language ought to be
       and Ltac1 was not designed following current PL conventions.

    2. The development of Ltac1 was not carefully planned, and features have been
       added piecemeal over time by different contributors.
       Consequently, the language is far from well-designed, uniform, or well
       implemented, making improvements and every day use complicated.

    3. Ltac1 tried to accommodate two contradictory features: for tactics
       to be both automagical and predictable.
       To do so, Ltac1 implements many dynamic decision procedures to facilitate
       writing tactics that work well for small examples but do not scale well.

    With experience, there are several well-known design flaws with Ltac1:

    - **No type system.** Ltac1 is completely untyped. Any value can be passed to
      any function, and type errors are only caught at runtime, often with cryptic
      error messages. This makes writing large libraries and tactics and debugging
      very tedious.

    - **No data structures.** Ltac1 has no lists, no records, and no algebraic
      types. All state must be threaded through the goal or through side channels.

    - **Unclear Semantics.** It is hard to predict when a tactic will be
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

    Ltac2 is designed to be the replacement of Ltac1, and offers both a
    reliable and scalable tactic language for Rocq, while being as backward
    compatible as possible.

    Its core improvements over Ltac1 are:

    - It is a proper typed functional programming language of the Hindley–Milner
      family, similarly to OCaml, with type inference, algebraic data types,
      and a clear call-by-value semantics.

    - It has an explicitly typed Foreign Function Interface.
      This makes it easy to extend Ltac2 to expose and access primitives like unification,
      that were not accessible before, while providing better documentation for it.
      As a consequence, it is possible to do more in Ltac2 than in Ltac1.
      For instance, it is now possible to manipulate the goal state, and modify
      the set of goals under focus etc.

    - Quoting and unquoting between Rocq terms (Gallina) and Ltac2 values is now
      explicit and syntactically marked. It no longer relies on a hard-to-predict
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

    It comes with a Core Library that is meant to contain basic building blocks
    for creating complex tactics. The Core Library keeps evolving and may contain
    more exposed primitives in more recent versions of Rocq.
    See https://github.com/rocq-prover/rocq/tree/master/theories/Ltac2 for
    the master branch of Rocq.
    Most notably, Ltac2 still lacks notations for some of the basic tactics.

    For the moment, Ltac2 is not loaded by default with the Prelude.
    It needs to be imported with [From Ltac2 Require Import Ltac2].
    Additional modules can be required or imported if needed.
*)

From Ltac2 Require Import Ltac2 Printf Option.

(** ** 2. Using Ltac2 to Write Proofs

    Before discussing the Ltac2 language itself, let us consider
    the differences between Ltac1 and Ltac2 proof modes, and how to use one
    in the other.

    *** 2.1 Using Ltac2 in the Ltac1 Proof Mode

    The main use for Ltac2 is to write predictable tactics.
    Yet, you do not need to port your whole development to Ltac2 to benefit from Ltac2.
    You can write new scripts in Ltac2 but call them in the usual Ltac1 proof mode.
    This lets you enjoy Ltac2's type safety and expressiveness while
    leaving all existing proofs untouched, and avoid dealing with differences
    between Ltac1 and Ltac2's proof mode.

    Consequently, a natural approach when migrating a large development is:
    1. Write new scripts in Ltac2 or port existing Ltac1 ones to Ltac2.
    2. Import them into Ltac1 via [ltac2:(...)].
    3. Use them in existing proof scripts without further changes.

    Importing Ltac2 automatically sets the proof mode to Ltac2.
    You can decide to keep using Ltac1 proof mode by using [Set Proof Mode "Classic"].
    Conversely, [Set Proof Mode "Ltac2"] to use the Ltac2 proof mode.
    You can then write scripts in Ltac2, and call them in a Ltac1 proof using
    [ltac2:()] wrapper.

    As an example, let us leverage the [printf] function for Ltac2.
*)

Ltac2 greet_and_close () :=
  printf "closing goal with exact true";
  exact true.

(** We can verify the Ltac2 function itself works in a Ltac2 proof: *)

Goal bool.
Proof.
  greet_and_close ().
Qed.

(** To call it from a Ltac1 proof script, wrap it with [ltac2:(...)].
    The Ltac2 expression inside must have type [unit]: *)

(* set the default mode to Ltac1 *)
Set Default Proof Mode "Classic".

Ltac use_ltac2_in_ltac1 :=
  ltac2:(greet_and_close ()).

Goal bool.
Proof.
  use_ltac2_in_ltac1.
Qed.

(** Importantly, [ltac2:(...)] creates a scope boundary: the code inside is pure
      Ltac2, and Ltac1 variables are not in scope there.

    For instance, in a function [my_intro (id : ident) := ltac2:(intro id)], the
    [id] inside [ltac2:(...)] would be treated as the Ltac2 literal name [id],
    not as the Ltac1 variable -- so the tactic would always introduce a
    hypothesis named [id] regardless of what was passed.

    To pass Ltac1 values across this boundary, one uses the binder syntax
    [ltac2:(x1 .. xn |- expr)], which explicitly receives Ltac1 values as Ltac2
    arguments and binds them under the names [x1 .. xn] in the Ltac2 scope.
    Inside the expression, [x1 .. xn] have type [Ltac1.t] and are converted to
    typed Ltac2 values using helpers such as [Ltac1.to_constr] and [Ltac1.to_ident].
    The Ltac2 wrapper must then be defined as a let-in and applied, due to Ltac1's inner workings.
*)

Set Default Proof Mode "Classic".

Ltac my_exact t :=
  let f :=
    ltac2:(t |-
      let t := Option.get (Ltac1.to_constr t) in
      exact $t)
  in f t.

Goal bool.
Proof.
  my_exact true.
Qed.

(** *** 2.2 Using the Ltac2 Proof Mode

    The first possibility is to use Ltac2 proof mode directly.
    It is very similar to Ltac1 outside of a few syntax changes.

    Most noticeably, the dispatching syntax has changed.
    In Ltac1, when a tactic creates more than one new goal, you can specify which
    tactic to apply with the syntax [tac1; [tac21 | tac22]].
    Moreover, [tac1; tac2; [tac31 | tac32]] is parsed as
    [(tac1; tac2); [tac31 | tac32]].
*)

Set Default Proof Mode "Classic".

Goal forall P Q R S : Prop, P -> Q -> R -> S -> (P /\ Q) /\ (R /\ S).
Proof.
  intros P Q R S HP HQ HR HS.
  split; split; [exact HP | exact HQ | exact HR | exact HS].
Qed.

(** In Ltac2, this is now written with the syntax [tac1 > [tac21 | tac22]] in order
    to avoid syntax conflict with ???. Moreover, [tac1; tac2; [tac31 | tac32]]
    is now parsed as [tac1; (tac2; [tac31 | tac32])] as Ltac2 no longer
    automatically delays tactic execution.

    Consequently, if [tac1] generates multiple goals, the dispatcher will
    attempt to apply the list [tac31|tac32] to the subgoals generated by [tac2]
    independently for each goal produced by [tac1].
    This typically results in an "Incorrect number of goals" error. To achieve
    standard Ltac1 factoring, you must use parentheses to explicitly group the
    sequence: (tac1; tac2) > [foo|bar].
*)

Set Default Proof Mode "Ltac2".

Goal forall P Q R S : Prop, P -> Q -> R -> S -> (P /\ Q) /\ (R /\ S).
Proof.
  intros P Q R S HP HQ HR HS.
  Fail split; split > [exact HP | exact HQ | exact HR | exact HS].
  (split; split) > [exact HP | exact HQ | exact HR | exact HS].
Qed.


(** Similarly, some tactic combinators now parse as if they were normal functions.
    Parentheses are now required around complex arguments, such as abstractions.
    The tacticals affected are: [try], [repeat], [do], [once], [progress], [time], [abstract].

    For instance, [try exact HP] is now parsed as [(try exact) HP]: [try] receives
    [exact] as its sole argument, and [HP] is left dangling, causing an error.
    It is hence required to write [try (exact HP)]. Respectively for the others.
*)

Set Default Proof Mode "Classic".

Goal forall P : Prop, P -> P.
Proof.
  intros P HP. try exact HP.
Qed.

Set Default Proof Mode "Ltac2".

Goal forall P : Prop, P -> P.
Proof.
  intros P HP.
  Fail try exact HP.
  try (exact HP).
Qed.

Goal forall P : Prop, P -> P.
Proof.
  intros P HP.
  Fail do 1 exact HP.
  do 1 (exact HP).
Qed.

(** However, a real issue with the Ltac2 proof mode is that some tactics
    are imported but are currently missing notations for them in the Corelib.
    For instance, in Rocq 9.0, a notation is missing for the tactic [clearbody].
    This problem will be solved over time with contributions to the Corelib.
*)

Goal forall A, A -> A * A.
Proof.
  intros. pose (x := 2). Fail clearbody x.
Abort.

(** In the meantime, there are two workarounds.

    The first option is to define the missing notation locally.
    In this case, one should also consider contributing it upstream to the Corelib.
    The underlying primitive lives in [Std] and expects an [ident list], so a
    notation using the [list1(ident)] parser -- which parses one or more
    space-separated identifiers -- is sufficient.
    See the corresponding section for more information.
*)

Ltac2 Notation "clearbody" ids(list1(ident)) := Std.clearbody ids.

Goal forall A, A -> A * A.
Proof.
  intros. pose (x := 2). clearbody x.
Abort.

(** The second option is to call the tactic through the Ltac1 compatibility
    bridge using [ltac1:(...)].
    This is the simplest workaround when you only need the tactic occasionally
    and do not want to introduce a local notation, but it comes with the usual
    caveats of mixing Ltac1 and Ltac2 (no type checking, limited interoperability
    with Ltac2 values).
*)

Goal forall A, A -> A * A.
Proof.
  intros. pose (x := 2). ltac1:(clearbody x).
Abort.

(** More generally, any Ltac1 tactic can be embedded into Ltac2 using [ltac1:(...)].
    The resulting Ltac2 expression has type [unit] and runs the Ltac1 tactic on
    the current goal.

    However, [ltac1:(...)] creates a scope boundary: the code inside is pure
    Ltac1, and Ltac2 variables are not in scope there. For instance, in a
    function [my_intro (id : ident) := ltac1:(intro id)], the [id] inside
    [ltac1:(...)] would be treated as the Ltac1 literal name [id], not as the
    Ltac2 variable -- so the tactic would always introduce a hypothesis named
    [id] regardless of what was passed.

    To pass Ltac2 values across this boundary, one uses the binder syntax
    [ltac1:(x1 .. xn |- tac)], which explicitly receives Ltac2 values as Ltac1
    arguments and binds them under the names [x1 .. xn] in the Ltac1 scope.
    The resulting expression has type [Ltac1.t -> .. -> Ltac1.t -> unit] and
    must be applied to the Ltac2 values, converted to [Ltac1.t] using helpers
    such as [Ltac1.of_constr] and [Ltac1.of_ident].
*)

Ltac2 my_exact (t : constr) :=
  ltac1:(t |- exact t) (Ltac1.of_constr t).

Goal 1 + 1 = 2.
Proof.
  my_exact '(eq_refl).
Qed.

Ltac2 my_intro0 (id : ident) :=
  ltac1:(id |- intro id) (Ltac1.of_ident id).

Ltac2 Notation "my_intro" id(ident) := my_intro0 id.

Goal forall n : nat, n = n.
Proof.
  my_intro n. reflexivity.
Qed.



(** ** 3. Ltac2 Is a Proper Functional Programming Language *)

(** Ltac1 is a non standard tactic language with no type system, opaque
      dynamically-typed values, and a non-standard evaluation strategy, making
      tactics fragile and hard to predict and debug.

    In contrast, Ltac2 is a proper programming language that belongs to the
    well-known class of ML languages: it is a call-by-value functional language
    with a Hindley–Milner type system.
    Expressions have static types that can be inferred, so ill-typed programs
    are rejected at compile time rather than at runtime.
    Moreover, evaluation is fully predictable thanks to call-by-value semantics.
    This makes Ltac2 tactics reliable and composable by design, as opposed to Ltac1.
*)

(** *** 3.1 Types and Type Inference

    The most fundamental difference between Ltac1 and Ltac2 is that Ltac2 is a
    statically typed language with Hindley–Milner type system, similarly to OCaml.

    In Ltac1 there is no type system: values are opaque and type errors are only
    caught at runtime with cryptic messages. In Ltac2, every expression has a
    type, and ill-typed programs are rejected before they are run. Type
    annotations are optional -- the type checker infers them -- but can be written
    for documentation or disambiguation.

    For instance, if we define an alias for integer addition, Ltac2 will
    automatically figure out the type is `int -> int -> int`:
*)

Ltac2 add (x : int) (y : int) : int := Int.add x y.
Ltac2 Eval add 2 3.
Fail Ltac2 Eval add 2 true.

(** Ltac2 supports Hindley–Milner polymorphism, also called prenex polymorphism.
    In prenex polymorphism, type-variable quantifiers must appear at the
    outermost level of the type, never nested inside it.

    For instance, [∀ 'a, 'a -> 'a] is a valid polymorphic type: the quantifier
    is at the front, and the function works at any type ['a]. It is the type of
    a function that takes an input of type ['a] and returns a value of the same type.

    However, [∀ 'a, (∀ 'b, 'b -> 'b) -> 'a] is not valid because ['b] is
    quantified inside the type. Note that it is not the same as [∀ 'a 'b, ('b -> 'b) -> 'a].
*)

Ltac2 my_id (x : 'a) : 'a := x.
Ltac2 Eval my_id 42.
Ltac2 Eval my_id true.

(** Ltac2 provides the following primitive types:
    - [unit]: the unit type, with its single value [()].
    - [bool]: Booleans, with values [true] and [false].
    - [int]: machine integers (63-bit on a 64-bit platform).
    - [string]: character strings.
    - [ident]: Rocq identifiers (names of hypotheses, variables, …).
    - [constr]: type of Rocq terms in Ltac2.

  Beyond the built-in types, you can define your own algebraic data
  types with [Ltac2 Type]. As in OCaml, constructor names must start with an
  **uppercase** letter ([Some], [None], [S], [O], …), while variable and
  function names **must** start with a **lowercase** letter.
  For instance, a type for arithmetic expressions can be defined by:
*)

Ltac2 Type rec expr :=
  [ Num(int)
  | Add(expr, expr)
  | Mul(expr, expr)
  ].

Fail Ltac2 foo X := X.

(** Functions can then be defined with the [rec] keyword for recursion,
    and [match] for pattern-matching similarly to OCaml.
    Constructors are then referred to without parentheses, like [Add a b].
*)

Ltac2 rec eval_expr (e : expr) : int :=
  match e with
  | Num n      => n
  | Add a b => Int.add (eval_expr a) (eval_expr b)
  | Mul a b => Int.mul (eval_expr a) (eval_expr b)
  end.

(* 1 + 2×3 = 7 *)
Ltac2 Eval eval_expr (Add (Num 1) (Mul (Num 2) (Num 3))).

(** The CoreLib provides some of the usual polymorphic types like [list] and
      [option], and a few basic functions for them.
*)

Ltac2 Eval [1; 2; 3].
Ltac2 Eval List.map (fun x => Int.add x 1) [1; 2; 3].

(** [option] represents a possibly-absent value: [Some x] for presence and
    [None] for absence.  Here is a function returning the head of a list as an
    option, with pattern matching on the constructors of the [list] type: *)

Ltac2 safe_head (l : 'a list) : 'a option :=
  match l with
  | []     => None
  | h :: _ => Some h
  end.

Ltac2 Eval safe_head [1; 2; 3].
Ltac2 Eval safe_head ([] : int list).


(** *** 3.2 Call-by-Value Semantics and Thunking

    Ltac1 has an unclear, hard-to-predict evaluation order. Ltac2 is strictly
    **call-by-value**: function arguments are fully evaluated before the
    function body is entered.

    This makes behavior predictable and intuitive, but it has one important
    consequence for passing tactics as arguments. If you pass a tactic [t] as an
    argument to a function, [t] is evaluated -- i.e. executed -- immediately,
    before the body of the function has a chance to decide whether to use it. To
    illustrate this, consider a function that ignores its argument and does nothing:
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

(** *** 3.3 Effects: Printf and References

  Compared to Ltac1, Ltac2 has proper effects, notably printing and references.

  **** 3.3.1 Printf

  In Ltac1, [idtac] is the only way to print, and there is no mutable state.
  Ltac2 has a proper typed [printf].

  [printf] takes a format string with typed specifiers:
  - << i >>: prints an [int]
  - << I >>: prints an [ident]
  - << s >>: prints a [string]
  - << m >>: prints a [message]
  - << t >>: prints a [constr] (a Rocq term)
  - << a >>: prints a value of any type using a custom formatter [fun () x => ...]
  - << A >>: same as << a >> but the formatter takes no [unit] argument
  - << % >>: outputs a literal [%]

    This makes it much easier to inspect the proof state or debug automation
    than the [idtac] approach. For instance, here is a small tactic to
    print the type of a hypothesis. We will explain the exact syntax
    in the next section.
*)

Ltac2 print_type0 (h : ident) :=
  printf "the type of the hypothesis %I is %t" h (Constr.type (Control.hyp h)).

Ltac2 Notation "print_type" h(ident) := print_type0 h.

Goal nat -> bool -> True.
  intros a b.
  print_type a.
  print_type b.
Abort.

(** **** 3.3.2 Mutable References

    Ltac2 provides ML-style mutable reference cells of type ['a ref].
    A reference is a box holding a single mutable value of type ['a].
    References make it possible to accumulate state across tactic calls —
    something that pure functional code cannot express.

    The [Ref] module provides the following primitives:
    - [Ref.ref v]: creates a fresh reference initialised to [v].
    - [Ref.get r]: returns the current value of [r].
    - [Ref.set r v]: replaces the value stored in [r] with [v].
    - [Ref.update r f]: applies [f] to the current value and stores the result.

    For [int ref] specifically, [Ref.incr r] and [Ref.decr r] add or subtract 1.

    For example, here is a tactic that tracks how many hypotheses it clears:
*)

Goal forall (n m : nat), True.
  intros n m.
  let count := Ref.ref 0 in
  clear n; Ref.incr count;
  clear m; Ref.incr count;
  printf "cleared %i hypotheses" (Ref.get count);
  exact I.
Qed.

(** Note that mutations to a reference are **not rolled back on backtracking**.
    If a branch modifies a reference and then fails, the modification persists.
    Keep this in mind when combining references with backtracking tactics.
*)


(** *** 3.4 Exceptions

    Ltac2 has a built-in type [exn] for exceptions.
    Several exceptions are predefined in the standard library:
    - [Tactic_failure (msg : message option)] -- the standard tactic failure,
      raised by most combinators and by [fail].
    - [Out_of_bounds (msg : message option)] -- index out of range (e.g. list access).
    - [Division_by_zero] -- integer division by zero.
    - [Invalid_argument (msg : message option)] -- a function received an argument
      it cannot handle.
    - [Match_failure] -- an inexhaustive pattern match was not satisfied.

    The [exn] type is open: you can add your own variants with the
    syntax [Ltac2 Type exn ::= [myEx (type)]].
*)

Ltac2 Type exn ::= [ OutOfFuel (message option) ].

(** The easiest method to build a value of type [message] is to use [fprintf],
    which works exactly like [printf] except it returns a [message] value
    instead of printing it.

    There are two primitives to raise an exception, with different semantics:

    1. [Control.throw : exn -> 'a] -- raises a **non-backtrackable** exception.
       It cannot be caught by the backtracking combinators [Control.plus] or
       [try]. It is meant for programming errors or hard failures where retrying
       makes no sense (analogous to a panic).
*)

Goal False.
  Fail try (Control.throw (OutOfFuel (Some (fprintf "should fail")))).
Abort.

(** 2. [Control.zero : exn -> 'a] -- raises a **backtrackable** exception.
      It signals that the current branch has no solution, which triggers
      backtracking: [Control.plus] will try the alternative branch, and [try]
      will silently recover. See the corresponding section for more information.
*)

Goal False.
  try (Control.zero (OutOfFuel (Some (fprintf "should succeed and print nothing")))).
Abort.



(** ** 4. Ltac2 as a Meta-Programming Language for Rocq *)

(** *** 4.1 Foreign Function Interface

    In Ltac1, all interaction with the Rocq codebase happens through built-in
    tactics imported as a single opaque block -- no types, no control over what
    is in scope.

    Ltac2 has an explicit, typed Foreign Function Interface (FFI).
    Rocq API -- kernel or higher-level functions -- can be easily exposed.
    This enables easy access to APIs that were not accessible in Ltac1,
    making Ltac2 much more expressive.

    Many APIs are exposed in different modules in the core library available at:
    https://github.com/rocq-prover/rocq/tree/master/theories/Ltac2

    Most notable examples:
    - [Control]: interact with the proof state (goal) and backtracking
    - [Constr]: inspect, build, and compare Rocq terms
    - [Std]: reduce terms, call unification, access the environment
    - [Fresh]: to create fresh [ident]
    - [Unification]: to call unification in a controlled way
    - [Constr.Unsafe]: to access the raw kernel representation of terms

    The full core library is at:
    https://github.com/rocq-prover/rocq/tree/master/theories/Ltac2

    For example, [Constr.type] retrieves the type of a term and [Std.eval_hnf]
    reduces it to head-normal form:
*)

Ltac2 print_hnf_type0 (h : ident) : unit :=
  let th := Control.hyp h in
  let ty_h := Constr.type th in
  let hnf_ty_h := Std.eval_hnf ty_h in
  printf "the hnf of the type of %I is %t" h hnf_ty_h.

Ltac2 Notation "print_hnf_type" h(ident) := print_hnf_type0 h.

Goal (let x := 1 in x = 1) -> False.
  intros x. print_hnf_type x.
Abort.


(** *** 4.2 Matching Terms and Goals

    Ltac1 provides [lazymatch], [match] and [multimatch] for matching
    patterns and goals. This still exists in Ltac2 but has changed syntax to
    avoid confusion with the [match] for matching algebraic types.

    The new syntax is [lazy_match!], [match!], and [multi_match!].
    Ltac2 provides three matching combinators:

    - [lazy_match! goal] -- like Ltac1 [lazymatch goal]: tries patterns in order,
      does **not** backtrack into a branch once a pattern has matched.
    - [match! goal] -- like Ltac1 [match goal]: tries patterns in order, and
      **does** backtrack into a branch if it raises an exception.
    - [multi_match! goal] -- backtracks both into branches and into patterns.

    Although it is common in Ltac1 to use uppercase variables for hypotheses, like [H],
    in Ltac2 you need to use **lowercase** ones.
*)

Ltac2 print_all_hyp () :=
  match! goal with
  | [h : ?t |- _] => printf "the hypothesis %I has type %t" h t; fail
  | [ |- _] => ()
  end.

Goal nat -> bool -> 0 = 1 -> False.
  intros. print_all_hyp ().
Abort.

(** Another difference with Ltac1 is that a pattern containing variable bindings
    must now be explicit, whereas it used to be optional and dynamically
    figured out if not specified. For instance, to match [let var := ?expr in
    ?body], one must write [let var := ?expr in @?body var].
*)

Ltac2 print_body_hyp_letin () : unit :=
  lazy_match! goal with
  | [_ : let var := _ in @?body var |- _]  =>
      printf "the body is expanded as a function: %t" body
  end.

Goal forall x y : nat, (let a := x + 2 in let b := y + 1 in a = b) -> True.
  intros. print_body_hyp_letin ().
Abort.


(** *** 4.3 Quoting and Unquoting

    One of the main sources of confusion in Ltac1 is the implicit boundary
    between Gallina (the language of Rocq terms) and Ltac1 meta-programs.
    Ltac1 uses dynamic scoping rules to resolve names, leading to subtle bugs
    when a name is mistaken for a Rocq term instead of an Ltac1 variable, or
    vice versa.

    The goal was to ease users' lives, but in practice this does not scale well.
    To fix this, Ltac2 makes this boundary **explicit** through quoting and unquoting operators.

    For example, a tactic that splits a conjunction and closes both goals with [I]:
*)

Ltac ltac1_close_conj t := split; exact t.

Set Default Proof Mode "Classic".

Goal True /\ True.
Proof.
  ltac1_close_conj I.
Qed.

(** In Ltac2, every Rocq term must be explicitly **quoted** with ['] which
    produces a Ltac2 term of type [constr], and **unquoted** to recover a Rocq term.

    If we wanted to rewrite [ltac1_close_conj] in Ltac2, we would take variable
    [t : constr] as argument, as [constr] is the only type we can manipulate.
    Yet, to apply it to [exact] which expects a Rocq term, we need to unquote it.
    This gives us:

*)

Ltac2 ltac2_close_conj0 (t : constr) := split; exact $t.

Set Default Proof Mode "Ltac2".

(** To be able to use it with a Rocq value, one then need to quote it to a [constr].
    For instance, like the following.
*)

Goal True /\ True.
Proof.
  ltac2_close_conj0 'I.
Qed.

(** The quoting can be done automatically using a notation, we refer to the
    following section for further explanations.
*)

Ltac2 Notation "ltac2_close_conj" t(constr) := ltac2_close_conj0 t.

(** The same applies to Rocq identifiers, which can be created using [@].
    In Ltac1, you could just write:
*)

Set Default Proof Mode "Classic".

Ltac ltac1_print_hyp_type h :=
  let T := type of h in idtac "type:" T.

Goal nat -> False.
Proof.
  intros H.
  ltac1_print_hyp_type H.
Abort.

(** In Ltac2, hypothesis names have the dedicated type [ident].
    Write [@name] to create an [ident] literal, then use [Control.hyp] to
    recover the corresponding [constr]:
*)

Set Default Proof Mode "Ltac2".

Ltac2 ltac2_print_hyp_type (h : ident) :=
  printf "type: %t" (Constr.type (Control.hyp h)).

Goal nat -> False.
Proof.
  intros H.
  Fail ltac2_print_hyp_type H.
  ltac2_print_hyp_type @H.
Abort.



(** *** 4.4 Backtracking

    Ltac1 controls backtracking through:
    - [match goal] (backtracks into branches on failure, etc.),
    - Combinators like [first [tac1 | tac2 | ...]]
    - [fail n] (propagates failure [n] levels up through [match] branches)

    Ltac2 has more fine-grained controls on backtracking.
    Matching and combinators are still available.
    However, [fail n] is no longer supported; it was a hack to deal with the lack
    of good primitives for backtracking.
    Instead, Ltac2 has fine-grained primitives to manipulate values
    as streams of possibilities and backtracking.
    Combinators like [first] can then be reimplemented using these primitives.

    Most users do not need these primitives, and the existing
    combinators are enough. We mention them briefly, and refer to the
    documentation for more details. The three primitives are:

    - [Control.zero : exn -> 'a] -- raises an exception and triggers backtracking.
      This is the primitive underlying Ltac2 [fail].

    - [Control.plus : (unit -> 'a) -> (exn -> 'a) -> 'a] -- stacks a backtracking
      choice: try the first thunk; on exception, try the handler.
      This is the primitive underlying [tac1 + tac2], but it is finer
      since different decisions can be performed depending on the exception raised.

    - [Control.case : (unit -> 'a) -> ('a * (exn -> 'a)) result] -- inspects
      whether a tactic has at least one success without consuming it.


    *** 4.5 Notations

    Ltac2 supports two kinds of custom syntax via [Ltac2 Notation].

    An **abbreviation** is a [Ltac2 Notation] with no argument clause; it
    simply expands to a fixed Ltac2 expression.
    It does not add a new rule to the Ltac2 grammar nor new keywords:
    the name is resolved as a plain identifier at parse time, so it cannot
    cause parsing conflicts, e.g. with variable names.
    It should be used when you want a short name for a combinator or a
    fixed tactic sequence.

    In Rocq 9.2 or above, use [Ltac2 Abbreviation].
*)

Ltac2 Notation obvious := first [assumption | reflexivity].

Goal 1 = 1 /\ True.
  split; obvious.
Qed.

(** A full [Ltac2 Notation] declares new parsing rules and keywords which are
    specified with ["tac_name"]. Arguments are then given with the syntax
    [name_arg(X)] and [X] specifies that type of [name_arg].

    The available argument parsers include:

    The basic atoms are:
    - [tactic] / [tactic(n)] -- parse a tactic at precedence level [n]
      (default 5); evaluated eagerly, so use [thunk] when the argument is a
      tactic branch that must be delayed.
    - [thunk(e)] -- parse [e], then wrap the result in [fun () => ...].
      The most common form is [thunk(tactic)], which turns each tactic
      argument into a [unit -> unit] thunk to prevent premature evaluation.
    - [ident] -- parse a plain identifier (type [ident]).
    - [constr] -- parse a Rocq term (type [constr]).
    - [string] -- parse a string literal (type [string]).
    - [int] -- parse an integer literal (type [int]).

    There also are combinators for optional arguments and list of arguments:
    - [list0(e)] -- parse a whitespace-separated, possibly empty, list of [e]
    - [list0(e, "sep")] -- same, but with a literal keyword separator [sep].
    - [list1(e)] / [list1(e, "sep")] -- like [list0] but require at least one
      element. The notation [my_first [...]] below uses
      [list1(thunk(tactic(6)), "|")] to parse one or more [|]-separated
      tactic branches.
    - [opt(e)] -- parse an optional argument [e] of type [option e]
    - [seq(e1, e2, ...)] -- parse a fixed sequence of entries and bind them as a tuple.

  As an example consider reimplementing [first] using the backtracking operators
  as implemented in the CoreLib.
*)

Ltac2 rec my_first0 tacs :=
match tacs with
| [] => Control.zero (Tactic_failure None)
| tac :: tacs => Control.enter (fun _ => orelse tac (fun _ => my_first0 tacs))
end.

(** To write a notation for it, we write:

    - ["my_first"] and ["["] / ["]"] are literal keywords that the parser matches
      verbatim; so that [my_first [...]] is unambiguous

    - [tacs] is the name bound in the body to the parsed argument

    - [list1(..., "|")] parses a non-empty list of elements separated by [|].

    - [tactic(6)] parses one tactic branch at precedence level 6.
      Level 6 is high enough to accept most compound tactics, yet low enough
      that the parser stops at [|] and ["]"] instead of consuming them.

    - [thunk(...)] wraps the parsed branch in [fun () => ...], so each branch
      is turned into a thunk [unit -> unit].  Without [thunk], every branch
      would be executed eagerly -- before [my_first0] even runs -- which would
      defeat the whole purpose of trying alternatives one by one.

    The result is that [my_first [t1 | t2 | t3]] is elaborated to
    [my_first0 [(fun () => t1); (fun () => t2); (fun () => t3)]].
    All together, it gives us the notation:
*)

Ltac2 Notation "my_first" "[" tacs(list0(thunk(tactic(6)), "|")) "]" := my_first0 tacs.

Goal True.
  my_first [ (printf "tactic 1"; fail) | (printf "tactic 2"; fail) | exact I ].
Qed.



(** ** 5. Small Case Study

    Let us now consider a small case study and write a tactic [simplify_let]
    that takes a hypothesis [h] whose type is a let-in [let var := expr in
    body[var]], and turns it into [body[x']], where [x' := expr] is a new shared
    definition introduced in the whole context and goal.

    In Ltac1, it would have been written as:
*)

Ltac simplify_let H :=
  let H := lazymatch goal with [ H : let var := ?t in _ |- _ ] => H end in
  let type_h := type of H in
  lazymatch type_h with
  | let var := ?expr in ?body =>
      idtac body;
      let x := fresh "x" in
      set (x := expr) in *;
      change (body x) in H;
      lazy head beta in H
  end.

(** In Ltac2, we need to:
    - **use lowercase for variables**
    - use [Control.hyp] to recover the body of h
    - [Constr.type] is now a proper function rather than an ad-hoc construction
    - use the [Fresh] module to create fresh variables
    - use [$] to unquote variables back to Rocq's world

  In the end, this gives us a script that is similar but with a few
  decorations and clearer semantics, which can be written with or without
  importing the modules.

*)

Import Control Constr.

Ltac2 simplify_let (h : ident) : unit :=
  let type_h := type (hyp h) in
  lazy_match! type_h with
  | let var := ?expr in @?body var =>
      printf "the body is :%t" body;
      let x := Fresh.in_goal @x in
      set ($x := $expr) in *;
      let x := hyp x in
      change ($body $x) in h;
      lazy head beta in h
  end.

(** The advantage of Ltac2 is that the FFI interface enables us to write scripts
    we could not have in Ltac1. For instance, we can now use the [Constr.Unsafe]
    API to write the [simplify_let] tactic by directly accessing the structure
    of the term, and performing the substitution by hand rather than relying on
    high-level tactics like [lazy head beta].
*)
Import Unsafe.

Ltac2 simplify_let_bis (h : ident) : unit :=
  let type_h := type (hyp h) in
  match kind type_h with
  | LetIn _ expr body =>
      let x := Fresh.in_goal @x in
      set ($x := $expr) in *;
      let x := hyp x in
      let new_body := substnl [x] 0 body in
      change ($new_body) in h
  | _ => fail
  end.
