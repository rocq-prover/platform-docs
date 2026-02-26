(** * Tutorial Equations : Dealing with indexed inductive types
  *** Main contributors

    - Thomas Lamiaux
    - Matthieu Sozeau
  *** Summary:

  [Equations] is a plugin for Rocq that offers a powerful support
  for writing functions by dependent pattern matching.
  In this tutorial, we focus on the facilities provided by [Equations] to
  define function by dependent pattern matching on indexed inductive types,
  and reason about them.

  In Section 1, we discuss indexed inductive types on the particularities
  of defining and reasoning about functions defined by pattern matching over
  them.
  In section 2, we discuss the no confusion property and how it enables to
  automatically discard impossible cases for indexed inductive types.
  In section 3, we discuss the particularity that indexed types have
  to particularise indices when matching, and issues that can arise.

  *** Table of content
  - 1. Basic Reasoning on Indexed Inductive Types
  - 2. Advanced Dependent Pattern Matching
    - 2.1 Discarding Automatically Impossible Cases
    - 2.2 The No-Confusion Properties
    - 2.3 The Tactic Depelim
  - 3. Unifying Indices and Inaccessible Patterns

  *** Prerequisites:

  Needed:
  - We assume basic knowledge of Rocq, of and defining functions by recursion
  - We assume basic knowledge of the plugin Equations, e.g, as presented
    in the tutorial Equations : Basics

  Not needed:
  - We discuss here indexed inductives but we recall the concept so previous
    knowledge about them is not needed

  Installation:
  - Equations is available by default in the Rocq Platform
  - Otherwise, it is available via opam under the name coq-equations

*)

From Equations Require Import Equations.

 (** ** 1. Basic Reasoning on Indexed Inductive Types

    Indexed inductive types are particular kind of inductive definitions
    Given a fixed parameter [A : Type], vectors define a family of linked
    inductive types.
    One of the most well-known examples of indexed inductive types are vectors.
    Given a fixed parameter [A : Type], vectors define a family of inductive
    types [vec A n : Type] indexed by natural numbers [n : nat] representing
    the lengths of the vectors.
    The Vector type has two constructors.
    The first constructor [vnil : vec A 0] represent the empty vector,
    logically of size [0].
    Given an element [a:A] and a vector [v : vec A n] of size [n], the
    second constructor [vcons] constructs a vector of size [n+1]
    [vcons a n v : vec A (S n)], intuitively by adding [a] at the beginning of [v].
*)

Inductive vec A : nat -> Type :=
  | vnil  : vec A 0
  | vcons : A -> forall (n : nat), vec A n -> vec A (S n).

Arguments vnil {_}.
Arguments vcons {_} _ _ _.

(** The difference between a parameter and an index is that a parameter is
    constant accross all the return types of the constructors, whereas an index
    changes in at least one of the return types.
    For instance, in the definition of vectors the type [A] is a parameter
    as it is constant across all the return types: [vec A 0] and [vec A (S n)].
    However, [n:nat] is an index as it is not constant in the returns types:
    in the return type of [vnil] it is fixed to [0], and in the return type of [vcons] it is [S n].
    Indices always appear after the [:] in an inductive type declaration.

    Reasoning about indexed inductive types like vectors is a bit more
    involved than for basic inductive types like lists as the indices can
    matter.
    Noticeably pattern matching on constructors of indexed inductive types
    like [vec A n] may particularise the indices.
    For instance, matching a vector [v : vec A n] to [vnil] forces the
    value [n] to be [0] while for [vcons] if forces [n] to be of the form
    [S m] for some integer [m].
    Consequently, when writing a function on an indexed inductive type,
    pattern-matching on the inductive type has an effect on other arguments
    of the function, specializing them.

    For instance, consider the definition of [vmap] and [vapp] :
*)

Equations vmap {A B} (f : A -> B) (n : nat) (v : vec A n) : vec B n :=
vmap f _ vnil := vnil ;
vmap f _ (vcons a n v) := vcons (f a) n (vmap f n v).

Print vmap.

Equations vapp {A} (n : nat) (v : vec A n) (m : nat) (v' : vec A m) : vec A (n+m) :=
vapp 0 vnil m v' :=  v';
vapp (S n') (vcons a n' v) m v' := vcons a (n'+m) (vapp n' v m v').

(* Here the only two possibly well-typed patterns when considering the [vnil] and [vcons]
  constructors are respectively with [n = 0] and [n = S n'] for some fresh [n'] variable. *)

(** Reasoning on indexed inductive is not very different from reasoning
    on regular inductive types except that we have to account for indices,
    which can in some cases cause some overheads.

    For basic properties as below, it makes no differences:
*)

Definition vmap_comp {A B C} (f : A -> B) (g : B -> C) (n : nat) (v : vec A n) :
           vmap g n (vmap f n v) = vmap (fun a => g (f a)) n v.
Proof.
  funelim (vmap f n v); simp vmap.
  - reflexivity.
  - f_equal. apply H.
Qed.

Lemma vmap_cong {A B n} (f f': A -> B) (v : vec A n) (Heq : forall (a:A), f a = f' a)
      : vmap f n v = vmap f' n v.
Proof.
  funelim (vmap f n v); simp vmap.
  - reflexivity.
  - now rewrite Heq, (H f').
Qed.

(** However, it can make some differences when operations on indices are
    involved as indices are relevant for simplification.
    For instance, if we try to prove that [vmap] respects [vapp] as below,
    in the [vcons] case simplification fails to simplify [vmap f (S n + m) ...].
    The reason is that the simplification rule associated to [vcons] is
    [vmap f (S n) (vcons a n v) = vcons (f a) n (vmap f n v)].
    Hence, [simp] can not simplify [vmap] until [S n + m] has been
    simplified to [S (n+m)] using [cbn].
    It then behaves as usual.
 *)

Definition vmap_vapp {A B} (n m : nat) (f : A -> B) (v : vec A n) (v' : vec A m) :
           vmap f (n+m) (vapp n v m v') = vapp n (vmap f n v) m (vmap f m v').
Proof.
  funelim (vmap f n v); simp vapp.
  - reflexivity.
  - (* Here we can see [simp] fails to simplify [vmap f (S n + m) ...] as
      [S n + m] is not of the form [S x] for some [x : nat].              *)
    simp vmap.
    (* We need to first simplify [+] using [cbn] :                         *)
    cbn.
    (* We can now simplify *)
    simp vmap vapp. now rewrite H.
Qed.

(** This is not a limitation of [Equations] itself. It is due to how the
    [rewrite] tactic behind [simp] unifies terms.

    In practice, indices are mostly inferable, so it is usually possible to
    make them implicit.
    It has the advantage to make the code much more concise.
    For instance, for [vec], it enables to write much shorter definitions
    of [vmap] and [vapp]:
*)

Arguments vcons {_} _ {_} _.

Equations vmap' {A B n} (f : A -> B) (v : vec A n) : vec B n :=
vmap' f vnil := vnil ;
vmap' f (vcons a v) := vcons (f a) (vmap' f v).

Equations vapp' {A n m} (v : vec A n) (v' : vec A m) : vec A (n+m) :=
vapp' vnil v' :=  v';
vapp' (vcons a v) v' := vcons a (vapp' v v').

(** Setting indices to be implicit also makes them implicit in proofs.
    Doing so is not an issue even in the case of [vmap_vapp] where
    we need to simplify indices to reduce.
    If we think a term should have been reduced but hasn't been because of
    indices, we can always make them temporally explicit to check.
    We can do so by defining an alias for the functions using the tactic
    [set (name_function_ex := @(name_function _ _ _))] with an underscore
    for the arguments we do not want to make explicit.
    After inspecting the goal, you can just erase the tactic or unfold
    the notations.
    As an example, let's reprove [vmap_vapp] :
*)

Definition vmap_vapp' {A B n m }(f : A -> B) (v : vec A n) (v' : vec A m) :
           vmap' f (vapp' v v') = vapp' (vmap' f v) (vmap' f v').
Proof.
  funelim (vmap' f v).
  - reflexivity.
  - simp vapp'.
    (* If we think [vmap' f (vcons a ...)] should have been simplified,
       we can set an alias to check if the index is of the form [S x]  *)
     set (vmap'_ex := @vmap' _ _).
     (* After inspecting the goal, you can just erase the tactic
        or unfold the alias                                           *)
     cbn. unfold vmap'_ex.
    (* It is now possible to simplify *)
    simp vmap' vapp'. f_equal. apply H.
Abort.

(** An alternative is to change the way [rewrite] looks for matching subterms
  in the goal, using the keyed unification strategy. With this setting, [rewrite (e : t = u)]
  looks for a syntactic match for the head of [t] in the goal but allows full
  conversion between arguments of [t] and the arguments of the matched application
  in the goal. This makes [simp] work up-to conversion of the indices.
  We can then directly call [congruence] to solve the induction case. *)

#[local] Set Keyed Unification.

Definition vmap_vapp_simp {A B n m }(f : A -> B) (v : vec A n) (v' : vec A m) :
           vmap' f (vapp' v v') = vapp' (vmap' f v) (vmap' f v').
  funelim (vmap' f v); simp vmap' vapp'.
  - reflexivity.
  - congruence.
Qed.

(** ** 2. Advanced Dependent Pattern Matching

    *** 2.1 Discarding Automatically Impossible Cases

    Having information directly part of typing, like the length for vector,
    can have advantages.
    Most noticeably, it can be used to exclude invalid cases automatically.
    For instance, consider the function tail that returns the last element.
    In the case of [list], the [tail] function has to return a term of type
    [option A] as there is no guarantee that the input is not the empty list.
    This is not necessary for vectors as we can use the index to ensure
    there is at least one element by defining tail as a function of type
    [vec A (S n) -> vec A n].
    This can be implemented very directly with [Equations] as [Equations] can
    deduce on its own that the [vnil] case is impossible :
*)

Equations vtail {A n} (v : vec A (S n)) : vec A n :=
vtail (vcons a v) := v.

(** Similarly, we can give a very short definition of a function computing
    the diagonal of a square matrix of size [n * n] represented as a
    vector of vector [v : vector (vector A n) n)].
    On the empty matrix it returns the empty list.
    On a matrix [(vcons (vcons a v) v')] of size [(S n) x (S n)] representing

    [[
              | a |     v     |
              |---------------|
              |       v'      |
              |               |
    ]]

    it returns [a] added to the diagonal of [vmap vtail v'], that is
    [v'] where the first column has been forgotten.

    Note, that in this case, pattern matching on [n] needs to be added to help
    Rocq see it is a strictly decreasing structurally recursive definition on the index.
    [vmap vtail v'] can otherwise not be recognized as a syntactic subterm of [v'].
    An alternative definition using well founded-recursion is presented below.
*)

Equations diag {A n} (v : vec (vec A n) n) : vec A n :=
diag (n:=O) vnil := vnil ;
diag (n:=S _) (vcons (vcons a v) v') := vcons a (diag (vmap vtail _ v')).

(** Thanks to [funelim], reasoning for this kind of programs is as usual
    to the difference that, as for function definitions, we only need to
    deal with the cases that are possible:
*)

Arguments vmap {_ _} _ {_} _.

Definition vmap_diag {A B n} (f : A -> B) (v : vec (vec A n) n) :
           vmap f (diag v) = diag (vmap (fun v' => vmap f v') v).
Proof.
  (* We start by induction, simplify and use the induction hypothesis *)
  funelim (diag v); simp vmap diag. 1: easy. rewrite H. f_equal.
  (* We simplify the goal by collapsing the different [vmap] using [vmap_comp],
     and notice the proof boils down to commutativity of [vtail] and [vmap] *)
  rewrite ! vmap_comp. f_equal. apply vmap_cong.
  (* There is left to prove by function elimination on [vtail] or [vmap]  *)
  intro v2. clear -v2. funelim (vtail v2). simp vmap vtail. reflexivity.
Qed.


(** *** 2.2 The No-Confusion Properties

    To do so, the elaboration procedure behind [Equations] relies crucially on
    no-confusion properties to deduce which cases are impossible, enabling to
    write concise code where all uninteresting cases are handled automatically.

    No-confusion properties basically embodies both discrimination and injectivity
    of constructors: they assert which equations are impossible because the head
    constructors do not match, or if they do match, simplify to equations between the
    constructor arguments.
    The cases above rely on the no-confusion property for [nat], that given
    [n], [m] returns [True] if [n] and [m] are both [0], [n = m] if they are both
    of the form [S n], [S m], and [False] otherwise.

    [Equations] provides a [Derive] command to generate this notion automatically
    for each inductive type.
    For instance, for [nat], it suffices to write:
*)

Derive NoConfusion for nat.
Print NoConfusion_nat.

(** You may have noticed that we have derived the no-confusion property for [nat]
    after defining [tail] and [diag], even though it is supposed to be necessary.
    This is because it is already defined for [nat] by default, so there was
    actually no need to do derive it in this particular case.

    [nat] is a very simple inductive type.
    In the general case, for indexed inductive types, there are two kind of no-confusion
    properties that can be derived by [Equations]:
    - The [NoConfusion] property that enables to distinguish object with different indices.
      It takes as argument objects in the total space [{n : nat & vec A n}] which is generated
      once and for all with `Derive Signature for vec`. It enables
      to solve general equations between objects in potentially different instances of the
      inductive family:
*)
Derive Signature for vec.
Derive NoConfusion for vec.
Check NoConfusion_vec.

(**
    - The [NoConfusionHom] property that enables to distinguish objects with the
      same indices (i.e., in the same instance of the inductive family), which
      is useful for simplifying homogeneous equations:
*)

Derive NoConfusionHom for vec.
Print NoConfusionHom_vec.

(** Note that you can also derive all of them at once using [Derive Signature NoConfusion NoConfusionHom for vec]. *)

(** While the [NoConfusionHom] property is derivable for many indexed inductive types,
    it is not the case that is derivable for all indexed inductive types.
    It is derivable only when equality of constructors can be reduced to equality
    of the non-forced constructor arguments. A forced argument of a constructor
    is a constructor argument (say of variable name [x]) that appears in a pattern
    position in an index of the constructor's type conclusion. Patterns are generated
    from variables and constructor applications in this case.

    For example on vectors, this corresponds to the fact that for [vcons a n v : vec A (S n)],
    [n] appears in a pattern position in [S n]. Intuitively, the value of the *forced*
    constructor argument [n] can be inverted from the type [vec A (S n)].
    [NoConfusionHom] for [vcons] proves that
    [vcons a n v = vcons a' n v' :> vec A (S n) <-> a = a' /\ v = v' :> vec A n],
    i.e. we can eliminate the trivial [n = n] equality on the forced argument [n].
    This ultimately relies on the [UIP] property for [nat] which shows that [forall e : n = n, e = eq_refl n].

    If it is not possible to derive it, then [Equations] may need the indices to
    satisfy Uniqueness of Identity Proofs, asserting that all equality proofs are
    equal, i.e. [UIP : forall (A : Type) (a b : A) (p q : a = b), p = q], to be able to
    elaborate the definition to a Rocq term.

    UIP holds for types like [nat] where equality is decidable, but it is not provable
    for all types. In particular, it is not provable for [Type] itself.
    It can be assumed as an axiom, but be mindful that while this is consistent with Rocq's
    vanilla theory and classical logic axioms, it is inconsistent with univalence, so you
    may not want to admit it globally in your development. Also, as for any axiom,
    it will result in stuck computations: [Equations] definitions relying on it will only be
    simplifiable using [simp] but no longer compute using e.g. [Eval compute].

    Consequently, [Equations] offers both options: you can declare it only for the types
    for which you can prove it or need it, or assume it globally:
*)

(** Assuming you can prove it, from e.g. decidability of equality *)
Definition uip_nat : UIP nat := eqdec_uip nat_EqDec.
Local Existing Instance uip_nat.

(** Dangerous, incompatible with univalence, and results in stuck computations. *)
Axiom uipa : forall A, UIP A.
Local Existing Instance uipa.

(** *** 2.3 No-confusion and Dependent Elimination Tactics *)
Require Import Arith.
Section Tactics.

(** [Equations] provides tactics to access the pattern-matching and simplification
  engines directly inside proofs.
  When indexed inductive types are involved, it often provides better simplification
  tactics than the default [injection] and [inversion] tactics, that can handle
  dependent cases.
*)

(** To explicit pattern-matching and control the naming of variables/hypotheses
  introduced by an elimination, it is possible to use the
  [dependent elimination] tactic, which provides access to the [Equations]
  pattern-matching notation inside proofs.
  Note that the syntax of the patterns for [dependent elimination] follows the
  syntax of Equation definitions clauses, rather than the Ltac tactics [as] clauses. *)

  Goal forall n m, n + m = m + n.
  Proof.
    induction n as [|n' IH]; intros m.
    dependent elimination m as [O|S m'].
  Abort.

  (** As for Equations definitions, the patterns should cover solely the possible
    values of the hypothesis. *)
  Goal forall a b (x : vec nat 2), (vcons a x = vcons b x) -> a = b.
  Proof.
    intros a b x H.
    (** [x : vec nat 2], so the only possible case to consider is two [vcons] applications
        ending with [vnil]. *)
    dependent elimination x as [vcons hd (vcons tl vnil)].
    (** [H : vcons a ... = vcons b ...] which implies [a = b]. [noconf H] applies
      no-confusion and substitution properties recursively to the type of [H] to
      simplify it, resulting in a substitution of [b] by [a] in the goal. *)
    noconf H. reflexivity.
  Qed.

  (* The [dependent elimination _ as _] tactic is robust: it will fail if the
    given patterns are non-exhaustive or contains unused clauses *)
  Goal forall a b (x : vec nat 2), (vcons a x = vcons b x) -> a = b.
  Proof.
    intros a b x H.
    (** [x : vec nat 2], so the only possible case to consider is
      two [vcons] applications ending with [vnil]. *)
    (* This pattern-matching is non-exhaustive for [x: vec A 2]*)
    Fail dependent elimination x as [vcons hd vnil].
    (* This pattern-matching contains an unused clause for [x : vec A 2]*)
    Fail dependent elimination x as [vcons hd (vcons tl vnil)|vcons hd vnil].
  Abort.

End Tactics.

(** ** 3. Unifying Indices and Inaccessible Patterns

    A particularity of indexed inductive types is that during pattern-matching
    indices may be particularised to values like variables or terms of
    the form [(f (...))], where [f] is not a constructor of an inductive type
    like [O] or [S].

    The most well-known of example of that is equality [| eq A x : A -> Prop |]
    that is _parameterized_ by a value [x] of type [A] and _indexed_
    by another value of type [A].
    Its single constructor states that equality is reflexive, so the only way
    to build an object of [eq x y] (in the empty context) is if [x] is
    definitionally equal to the term [y].

    [[
      Inductive eq (A : Type) (x : A) : A -> Prop :=
      | eq_refl : eq A x x.
    ]]

    Pattern-matching on the equality then unifies the index [y] with the
    parameter [x], that is to a variable.
    Consequently, we have determined the _value_ of the pattern [y] to be [x],
    and it is no longer a candidate for refinement with available constructors like
    [0] or [S n].
    Such a pattern is said to be "inaccessible", and needs to be indicated
    by writing [?(t)] to tell Equations not to refine it but rather check its
    inferrability.

    As an example, to prove the symmetry of equality we pattern
    match on an equality [H : x = y], which unify [y] the variable [x]
    that we indicate by writing [eq_sym x ?(x) eq_refl].
    The goal now being [x = x], it holds by [eq_refl].
*)

Equations eq_sym {A} (x y : A) (H : x = y) : y = x :=
eq_sym x ?(x) eq_refl := eq_refl.

(** In practice, when the values determined are variables as in [eq_sym],
    the inaccessibility annotation is optional and we can simply write [x]
    or a wild card [_] rather than [?(x)].
*)

Equations eq_trans {A} (x y z : A) (p : x = y) (q : y = z) : x = z :=
eq_trans x x x eq_refl eq_refl := eq_refl.

(** For an example, where the [?(t)] notation is needed, consider this inductive
    definition of the image.
    It has one constructor that for all elements [a:A] generates an element
    in its image by [f], [Imf f (f a)].
    Intuitively, it means that there is an object in [Imf f x] provided
    that [x] is of the form [f a] for some [a].
*)

Inductive Imf {A B} (f : A -> B) : B -> Type
  := imf (a : A) : Imf f (f a).

(** Pattern-matching on [im : Imf f t] particularise [t] to be of the form
    [f a] for some [a].
    As [f] is not a constructor, [f a] is inaccessible and we need to write
    as [?(f a)] in the pattern matching to prevent [Equations] to try to
    interpret [f] as a constructor.
    As an example, we can write a function returning the [a] associated
    to an object in the image :
*)

Equations inv {A B} (f : A -> B) (t : B) (im : Imf f t) : A :=
inv f ?(f s) (imf f s) := s.

(** Be careful that if you forget to mark inaccessible patterns, then [Equations]
    will try to match on the patterns, creating potentially pointless branches.
    It is fine in theory as the definition obtained will be logically equivalent
    provided elaboration succeeded, but annoying if you want to extract the code as the definition will be more involved.

    For instance, if we define [vmap''] by matching on [n] without marking the
    pattern associated to [n] as inaccessible, we can see at extraction that [Equations]
    matched [n] and end up with absurd branch to eliminates, yielding a more complicated
    definition than the original [vmap]:
*)

Equations vmap'' {A B} (f : A -> B) (n : nat) (v : vec A n) : vec B n :=
vmap'' f 0 vnil := vnil ;
vmap'' f (S n) (vcons a v) := vcons (f a) (vmap'' f n v).

Extraction vmap.
Extraction vmap''.

(** Using inaccessible patterns hence allows to separate explicitely the subjects of
  pattern-matchings and the inferred indices in definitions. The following alternative
  definition of the square matrix diagonal pattern-matches only on the [vec] argument,
  but uses well-founded recursion on the index [n] to justify termination, as
  [vmap vtail v'] is not a subterm of [v']. *)

Equations diag_wf {A n} (v : vec (vec A n) n) : vec A n by wf n :=
diag_wf (n:=?(O)) vnil := vnil ;
diag_wf (n:=?(S _)) (vcons (vcons a v) v') := vcons a (diag_wf (vmap vtail v')).

(* Again, one can observe the extractions of the two diagonal definitions to see
  that [diag_wf] is more efficient, not needing to pattern-match on the indices first. *)

Extraction diag.
Extraction diag_wf.
