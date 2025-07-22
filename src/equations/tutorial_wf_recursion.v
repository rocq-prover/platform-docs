(** * Well-founded Recursion using Equations

  *** Summary

  [Equations] is a plugin for %\cite{Coq}% that offers a powerful support
  for writing functions by dependent pattern matching.
  In this tutorial, we focus on the facilities provided by Equations to
  define function using well-founded recursion and to reason about them.

  In section 1, we explain the interests and the principle of well-founded recursion.
  We then explain in section 2, how to define functions and how to reason about
  them using well-founded recursion and [Equations].
  In some cases, applying well-founded recursion can fail because information
  relevant to termination get lost during recursion.
  In section 3, we discuss two such cases a how to go around them.

  *** Table of content

  - 1. Introduction to well-founded recursion
    - 1.1 The syntactic guard condition is limited
    - 1.2 Well-founded recursion
    2. Well-founded recursion and Equations
      - 2.1 Using a measure
      - 2.2 Using a lexicographic order
      - 2.3 Using a custom well-founded relation
  - 3. Different tricks to work with well-founded recursion
    - 3.1 The inspect method
    - 3.2 Improving recursion hypotheses

  *** Prerequisites

  Needed:
  - We assume basic knowledge of Coq, and of defining functions by recursion
  - We assume basic knowledge of the Equations plugin and of obligations, e.g,
    as presented in the tutorials Equations: Basics and Equations: Obligations

  Not needed:
  - This tutorial discusses well-founded recursion but no prior knowledge
    about it is required: we will explain the concept
  - To simplify proofs involving arithmetic, we use the automation
    tactics [lia] and [auto with arith], but they can be used as black boxes

  Installation:
  - Equations is available by default in the Coq Platform
  - Otherwise, it is available via opam under the name coq-equations

*)

From Equations Require Import Equations.
From Coq Require Import List Arith Nat Lia.
Import ListNotations.


(** ** 1. Introduction to well-founded recursion

    For Coq to be consistent, all functions must be terminating.
    To ensure they are, Coq checks that they satisfy a syntactic
    criterion named the guard condition.
    Roughly, the guard condition checks that all recursive calls are performed
    on arguments syntactically detected to be subterms of the original argument.
    While practical and powerful, this syntactic criterion is by nature
    limited and not complete: it can happen that functions can be proven terminating
    using size arguments and mathematical reasoning, even though the guard fails
    to see them as such.


    *** 1.1 The syntactic guard condition is limited

    A common pitfall is when a recursive call is obfuscated, that is when
    it is not performed directly on a subterm [x], but on a subterm to which a
    function has been applied [f x], preventing the syntactic guard
    from checking that it is still indeed smaller.

    For instance, consider the function [nubBy] below, that
    filters out the duplicates of a list.
    The recursive call is not performed on the recursive argument [l] but
    on the list [filter (fun y => negb (eq x y)) l]. This is too much for the guard
   and the function is hence rejected.
    Yet, we can prove that [filter] does not increase the size of a list, and hence
    that the recursive call is indeed performed on a "smaller" instance than [l]
    and that [nubBy] is terminating.
*)

Fail Equations nubBy {A} (eq : A -> A -> bool) (l : list A) : list A :=
nubBy eq []        => [];
nubBy eq (a :: l) => a :: nubBy eq (filter (fun b => negb (eq a b)) l).

(** Furthermore, it can also happen that the recursive structure of a definition
    do not follow the inductive structure of any datatypes, but instead
    fully rely on semantic arguments to decide which recursive call to
    perform, logically preventing the guard condition from checking it.

    A prime example is Euclide's algorithm computing the gcd of
    [x] and [y].
    It performs recursion on [x mod y], which is not a subterm of the inputs.
    Yet, it is terminating, because the sum of the two arguments is a sequence
    of natural numbers, which strictly decreases and thus cannot go forever.
    Consequently, there is no hope for a syntactic guard to accept [gcd] as
    its definition fully relies on theoretic reason to ensure termination.
*)

Fail Equations gcd (x y : nat) : nat :=
gcd x y with eq_dec y 0 => {
  | left _ => x
  | right _ => gcd y (x mod y)
}.

(** *** 1.2 Well-founded recursion

    **** Informally

    It would be limiting if this kind of functions could not be defined.
    Fortunately, they can be using well-founded recursion.

    Informally, defining a function [f] by well-founded recursion
    amounts to a usual definition, except that we justify termination by:
    - Providing a "well-founded" relation [R : A -> A -> Prop], informally a relation
      for which there is no infinitely decreasing sequence.
      For instance, the strict order on [nat], [< : nat : -> nat -> nat] is well-founded
      as starting from [m : nat], it impossible to decrease infinitely, there is a point
      at which you must reach [0].
    - Proving that all the recursive calls are performed on smaller arguments
      according to [R]

    This allows us to justify termination of our function [f]: since each recursive call
    is on a smaller argument, an infinite sequence of recursive calls would give an
    infinitely decreasing sequence according to [R], which by assumption cannot exist.

  **** More Formally

   In a type theory like Coq's, however, defining a well-founded relation as one
   "not having infinitely decreasing sequence" is slightly too weak too use properly.
   Instead, we use the stronger notion of "accessibility" to define
   well-founded relations [R : A -> A -> Prop]. This is classically equivalent to having no
   infinite decreasing sequence, but in an inductive definition which is much easier to use.

    An element [a : A] is accessible for [R], denoted [Acc R a] when
    all [a' : A] smaller than [a], [a'] are themselves accessible.
    Intuitively, it constructively ensures that they are no decreasing sequence
    as the only ways for an element [a] to be accessible are that:
    - 1. There are no elements smaller than [a], so you cannot decrease further
    - 2. All elements smaller than [a] are accessible, so there are no infinitely
         decreasing sequence from them, and hence from [a].
*)

Print Acc.

(** We then say a relation is well-founded, when [forall (a : A), Acc R a], that is
       when all inhabitants of [A] are accessible.
    It ensures that wherever we start at, we cannot decrease forever.
*)

Print well_founded.

(** Given a well-founded relation [R : A -> A -> Prop], defining a function
    [f] by well-founded recursion on [a : A] consists in defining [f] assuming that
    [f] is defined for all [a'] smaller than [a], that is such that [R a' a].
    When specialized to natural numbers and [<], this concept is sometimes
    known as "strong recursion / induction": when defining [f n] one assumes
    that [f] is defined/proven for all smaller natural numbers [n' < n].

    **** In practice

    There are several methods to define functions by well-founded recursion using Coq.
    They all have their pros and cons, but as a general rule defining functions
    and reasoning using well-founded recursion can be tedious.

    For instance, consider the [Fix] construction of the standard library,
    which is a direct type theoretic definition of the concept of well-founded recursion:

    [[
      Fix : ∀ [A : Type] [R : A -> A -> Prop], well_founded R ->
            ∀ P : A -> Type, (∀ x : A, (∀ y : A, R y x -> P y) -> P x) ->
            ∀ x : A, P x
    ]]

    We can use it to define [gcd] as:
*)

Lemma gcd_oblig: forall (a b: nat) (NE: b <> 0), lt (a mod b) b.
Proof.
Admitted.

Definition gcd_Fix (x y : nat) : nat :=
  Fix lt_wf (fun _ => nat ->  nat)
      (fun (b: nat) (gcd_Fix: forall b', b' < b -> nat -> nat) (a: nat) =>
          match eq_dec b 0 with
          | left EQ => a
          | right NE => gcd_Fix (a mod b) (gcd_oblig a b NE) b
          end)
      y x.

(** However, doing so has several disadvantages:

    The function is much less readable than a usual definition by [Fixpoint] as:
    - there is an explicit fixpoint combinator [Fix] in the definition
    - we are forced to use curryfication and change the order of arguments
    - explicit proofs now appears directly in the definition of the function
      (though [Program] can help for that)

    It also makes it harder to reason about the function as it forces to use recursion
    on the accessibility proof, which no longer corresponds to the way we think about
    our function.
    Moreover, as we had to use curryfication in our definition, we may need
    the axiom of function extensionally to reason about [gcd_Fix].

    To go around these different issues, Equations provides a built-in mechanism
    to help us write functions and reason by well-founded recursion.
*)


(** ** 2. Well-founded recursion and Equations

    To define a function by well-founded recursion with Equations, one must add
    after the type of the function [by wf x R], where [x] is the decreasing
    term, and [R] the well-founded relation for which [x] decreases,
    and then define the function **as usual**.

    For instance, the function [nubBy] terminates as the size of the list decrease
    in each recursive call according to the usual strict order [<] on [nat], [lt] in Coq.
    We hence need to write [wf (size l) l] to define it by well-founded recursion:

    [[
    Equations nubBy {A} (eq : A -> A -> bool) (l : list A) : list A by wf (length l) lt :=
    nubBy ... := usual_def;
    nubBy ... := usual_def.
    ]]

    Equations will then automatically:
    - 1. Search for a proof that [R] is well-founded, using type classes (a database)
         specific to [Equations] suitably named [WellFounded]
    - 2. Create an obligation to prove that each recursive call
         is performed on decreasing arguments, try to prove it automatically,
         and if it cannot do it on its own leave it for us to prove

    This allows to write our definition transparently and directly as we would like to.
    In particular, we do not need to alter the structure of the definition to
    get it accepted, and it allows us to separate the proofs that the recursive
    call are smaller from the definition, making it easier to read and define
    while automatically dealing with trivial cases.

    In the following, we assume basic knowledge of obligations and [Equations]
    works together as discussed in the (short) tutorial Equations: Obligations.

    ** 2.1 Using a measure

    The most basic (and actually very versatile) method to define a function by well-founded
    recursion is to define a measure into [nat] to use the well-founded order [<],
    that is a function [m : ... -> nat] depending on the arguments,
    and to prove the measure decreases in each recursive call.

   A simple example is the size of an inductive value, i.e. the maximal number of nested constructors.
    Is already enough to define the function [nubBy], that recursively filters
    out the duplicates of a list, by well-founded recursion.
    Indeed, the size of a list is its length, and the only recursive call
    performed by [nubBy] is on [filter (fun y => negb (eq x y)) l].
    As [filter] can only remove elements, its length is indeed smaller
    than [l]'s, and the function is terminating.

    To define [nubBy] using [Equations] and well-founded recursion, it suffices to
    add [wf (length l) lt] after typing to indicate on which term, here [length l], and
    for which well-founded relation, here [lt] (the relation behind the notation [<]),
    we wish to use well-founded recursion.
    An obligation corresponding to proving that the recursive call is smaller,
    that is [length (filter (fun y => negb (eq x y)) l) < length (a :: l)], is created.
    As [Equations] cannot solve on its own, it then left to us to solve.
    Using the keyword [Equations?], it is automatically unshelved,
    and we simply have to prove it using tactics.
*)

Equations? nubBy {A} (eq : A -> A -> bool) (l : list A) : list A by wf (length l) lt :=
nubBy eq []        => [];
nubBy eq (a :: l) => a :: nubBy eq (filter (fun b => negb (eq a b)) l).
Proof.
  eapply Nat.le_lt_trans.
  - apply filter_length_le.
  - auto with arith.
Qed.


(** Reasoning on functions defined with well-founded
    recursion with [Equations], is no different than on regular functions.
    Using function elimination ([funelim]) we can prove our properties directly
    according to the pattern of our definition.
    In particular, we do not have to do proofs by well-founded induction.
    This completely hides well-founded recursion and allows us to reason
    about our function directly as we think about it.

    This is a very powerful method that, for instance, enables us to prove in a
    few lines that [nubBy] does remove all duplicates.
*)

Lemma In_nubBy {A} (eq : A -> A -> bool) (l : list A) (a : A)
               : In a (nubBy eq l) -> In a l.
Proof.
  funelim (nubBy eq l); simp nubBy; cbn.
  intros [Heq | H0].
  - rewrite Heq. left; reflexivity.
  - specialize (H _ H0). apply filter_In in H as [Inal eqa].
    right; assumption.
Qed.

Lemma nubBy_nodup {A} (eq : A -> A -> bool) (l : list A) :
      (forall x y, (eq x y = true) <-> (x = y)) -> NoDup (nubBy eq l).
Proof.
  intros Heq; funelim (nubBy eq l).
  - simp nubBy. constructor.
  - specialize (H Heq). simp nubBy. constructor.
    -- intros Hi.
       apply In_nubBy in Hi.
       apply filter_In in Hi as [Hl Hneqx].
       specialize (Heq a a); destruct Heq as [_ Heqx].
       specialize (Heqx eq_refl); rewrite Heqx in Hneqx.
       inversion Hneqx.
    -- assumption.
Qed.

(** For a slighlty more involved consider a [gcd] function that does not require
    the assumption that [x > y], by first checking if [x] or [y] is [0], and otherwise
    compares [x] and [y], and recalls [gcd] with [x - y] or [y - x] depending on
    which is greater.
    We cannot prove it is terminating either by looking if [x] or [y] decreases
    (the size of a number is the number itself) as we do not know upfront which
    of [x] or [y] is bigger.
    However, we can use that the measure [x + y] is decreasing for the usual
    well-founded order on [nat], as if [x] and [y] are strictly greater than [0],
    then [x + y > x + (y - x) = y] and [x + y > y + (x - y) = x].

    We can define [gcd] by well-founded recursion by annotating the definition with [wf (x + y) lt].
    We then get two obligations corresponding to the recursive goals, which
    are basic arithmetic goals and can be solved using [lia].
*)

Equations? gcd (x y : nat) : nat by wf (x + y) lt :=
gcd 0 x := x ;
gcd x 0 := x ;
gcd x y with gt_eq_gt_dec x y := {
| inleft (left _) := gcd x (y - x) ;
| inleft (right refl) := x ;
| inright _ := gcd (x - y) y }.
Proof.
  all: lia.
Defined.

(** For further examples of how functional elimination works on well-founded
    recursion and how useful it is on complex definitions, we will now show a
    few properties of [gcd].
*)

Lemma gcd_same x : gcd x x = x.
Proof.
  funelim (gcd x x). all: try lia.
Qed.

Lemma gcd_spec0 a : gcd a 0 = a.
Proof.
  funelim (gcd a 0). all: reflexivity.
Qed.

Lemma mod_minus a b : b <> 0 -> b < a -> (a - b) mod b = a mod b.
Proof.
Admitted.

Lemma gcd_spec1 a b: 0 <> b -> gcd a b = gcd (a mod b) b.
Proof.
  funelim (gcd a b); intros.
  - now rewrite Nat.Div0.mod_0_l.
  - reflexivity.
  - now rewrite (Nat.mod_small (S n) (S n0)).
  - now rewrite refl, Nat.Div0.mod_same.
  - rewrite H; auto. now rewrite mod_minus.
Qed.


(** ** 2.2 Using a lexicographic order

    Not all definitions can be proven terminating using a measure and the strict order [<] on [nat].
    In some cases, it is more practical to use a different well-founded order.
    In particular, when a function involves recursion on different arguments but
    not all recursive arguments are smaller at once, it can be practical to use a
    lexicographic order [<lex].
    Given two order [<A : A -> A -> Prop] and [<B : B -> B -> Prop],
    [(a,b) <lex (a',b')] iff [a <A a'] or [a = a'] and [b <B b'].
    This is useful, as it suffices for one argument to decrease for the recursive
    call to be smaller.
    Moreover, [<lex] is well-founded as soon as [<A] and [<B] are.

    A classical example where it is useful, is to define the Ackerman function:
*)

Fail Equations ack (m n : nat) : nat :=
ack 0 n := S n;
ack (S m) 0     := ack m 1;
ack (S m) (S n) := ack m (ack (S m) n).

(** Indeed, it is terminating as the recursive call are all smaller for the
    lexicographic order, which is essential to deal with the last case:
    - [(m,0) <lex (S m, 0)] as [m < S m]
    - [(m, ack (S m) n) <lex (S m, S n)] as [m < S m]
    - [(S m, n) <lex (S m, S n)] as [S m = S m] and [n < S n]

    To define [ack] by well-founded recursion, it suffices to add [(lexprod _ _ lt lt)].
    The function [lexprod] builds the lexicographic order and derive a proof
    that it is well-founded provided that both order are.
    As we can see, with this order, the obligations generated turn out to be
    simple enough to be automatically dealt with by [Equations].
*)

Equations ack (m n : nat) : nat by wf (m, n) (lexprod _ _ lt lt) :=
ack 0 n := S n;
ack (S m) 0     := ack m 1;
ack (S m) (S n) := ack m (ack (S m) n).


(** Reasoning about [ack] works as usual whether the pattern is general or specialized:
*)

Definition ack_min {m n} : n < ack m n.
Proof.
  funelim (ack m n). all: eauto with arith.
Qed.

Definition ack1 {n} : ack 1 n = 2 + n.
Proof.
  funelim (ack 1 n); simp ack.
  - reflexivity.
  - rewrite H. reflexivity.
Qed.


(** ** 2.3 Using a custom well-founded relation

    In some cases, there is no basic order that easily lets one define a
    function by well-founded recursion.
    In this case, it can be interesting to:
    - 1. Define your own relation [R : A -> A -> Prop]
    - 2. Prove it is well-founded [wf_R : well_founded R]
    - 3. Declare it as an instance so that Equations can find it with
         [Instance name : WellFounded R := wf_R].

    For instance, suppose we have an infinite sequence [f : nat -> bool] of booleans,
    such that we know logically that there is at least one that is true
    [h : exists n : nat, f n = true].
    This is represented by this context:
 *)

Section LinearSearch.

Context (f : nat -> bool).
Context (h : exists m : nat, f m = true).

(** Knowing there exists an [m : nat] such that [f m = true], we would like to
    actually compute one.
    Intuitively, we should be able to just try them one by one starting from 0
    until we find one, and it should terminate as we know there exists a [m] such
    that [f m = true].
    However, it is not clear which classical measure or relation to use to
    formalise this intuition. We will hence use a custom relation [R n m].

    We want to distinguish whether [n < m] or [m <= n]:
    - When [m <= n], we do not care about [Acc n] as we are supposed to have already found [m].
      As we know that [f m = true], to discard these cases automatically, we add
      [forall k, k <= m -> f k = false] to the relation to get [f m = false].
    - By the previous point, we know that [Acc m].
      Consequently, to prove [Acc n] when [n < m], we want to reason by induction
      on [k := m - n]. To do so, we add [n = S m] to the relation.

    This gives us the following relation and proof of our intuition.
    Note that understanding the proofs doe not matter for this tutorial.
*)

Definition R n m := (forall k, k <= m -> f k = false) /\ n = S m.

Lemma wf_R_m_le m (p : f m = true) : forall n, m <= n -> Acc R n.
Proof.
  intros n H. constructor. intros ? [h' ?].
  specialize (h' m H).
  congruence.
Qed.

Lemma wf_R_lt_m m (p : f m = true) : forall n, n < m -> Acc R n.
Proof.
  intros n H.
  (* Prove Acc m *)
  assert (Acc R m) as Hm_acc by (eapply wf_R_m_le; eauto).
  (* Set up induction on k := m - n *)
  rewrite <- (Nat.sub_add n m) in * by lia.
  set (k := m - n) in *; clearbody k. clear p H.
  (* Proof *)
  induction k.
  - easy.
  - apply IHk. constructor. intros ? [? ->]. assumption.
Qed.

   (** We can now prove that the relation is well-founded: *)
Lemma wf_R : (exists n : nat, f n = true) -> well_founded R.
Proof.
    intros [m p] n. destruct (le_lt_dec m n).
    - eapply wf_R_m_le; eassumption.
    - eapply wf_R_lt_m; eassumption.
Qed.

(** Having proven it is well-founded, we declare it as an instance of the database
    [WellFounded] so that [Equations] can find it automatically when using the
    keyword [wf x R].
*)

Instance wfR : WellFounded R := wf_R h.

(** We are now ready to define our function by well-founded recursion.

    Here, for technical reason we use the [inspect] method to remember the value of [f m].
    Here, it is not necessary to understand it for our purpose, and we refer to
    section 2.1 for more details on the method.
 *)

Definition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.

Notation "x 'eqn' ':' p" := (exist _ x p) (only parsing, at level 20).

(** Even though we want to start a computation at 0, to define our function
    by well-founded recursion we need to start at a generic point [m : nat],
    to actually have a term to do our recursion on:
*)

Equations? exists_nat (m : nat) (H : forall n, n < m -> f n = false) :
  {n : nat | f n = true} by wf m R :=
exists_nat m H with inspect (f m) :={
  | true  eqn:p => (exist _ m p)
  | false eqn:p => exists_nat (S m) _
}.
Proof.
- inversion H0; auto.
- unfold R. split. 2: reflexivity.
  intros k ikm. inversion ikm. 1: assumption.
  subst. apply H. auto with arith.
Qed.

Theorem linear_search : {n : nat | f n = true}.
Proof.
  unshelve eapply (exists_nat 0).
  intros n Hn0; inversion Hn0.
Qed.

End LinearSearch.


(** ** 3. Different methods to work with well-founded recursion

    When defining a function, it can happen that we lose information
    relevant to termination when matching a value, and that we then get
    stuck trying to prove termination.

    In this section, we discuss two such example an methods to go around the issue.
    Note that the inspect method was already used in section 2.4.

    *** 3.1 The inspect method

    Working with a particular well-founded order [lt], it may happen that
    we have a choice function [f : A -> option A] that for any [(a :A)]
    returns [None] or a strictly smaller element.
    This situation is axiomatised by the following context :
*)

Section Inspect.

Context {A : Type} {lt : A -> A -> Prop} `{WellFounded A lt}.
Context (f : A -> option A) (decr_f : forall n p, f n = Some p -> lt p n).

(** In this case, given an element (a : A), we may be interested in computing
    the decreasing chain starting from [a] specified by [f].
    Naively, we would like to do it as follows:
    first, we check if there is an element smaller than [a] by matching [f a]
    with a [with] clause; if there is none, then we stop the computation, otherwise
    we get [Some p] and we returns [p] added to the chain starting with [p],
    i.e., our recursive call [f_sequence p].
*)

Equations? f_sequence (a : A) : list A by wf a lt :=
f_sequence a with (f a) := {
  | Some p => p :: f_sequence p;
  | None => nil
  }.
Proof.
  apply decr_f.
  (* What to do now ? *)
Abort.

(** Unfortunately, as we can see, by doing so we generate an unprovable
    obligation as we do not remember information about the call to [f n] being
    equal to [Some p] in the recursive call [f_sequence p].

    To go around this issue and remember the origin of the pattern,
    we can wrap our match with the [inspect] function, which simply packs a
    value with a proof of an equality to itself.
    In other words, given an element [(a : A)], [inspect (a)] returns the
    elements [(a, eq_refl) : {b : A | a = b}].
*)

Print inspect.

Notation "x 'eqn:' p" := (exist _ x p) (only parsing, at level 20).

(** In our case, wrapping with [inspect] means matching first on
    [inspect (f a)] then on the first component which is by definition [f a],
    rather than directly on the term [f a].
    This may seem pointless as if one destruct [f a] in an equality
    [f a = f a], one would surely get [Some p = Some p] and learn nothing?
    The trick here is that [inspect (f a)] returns an object of type
    [{b : A | f a = b}], type in which [f a] is a fixed constant.
    Consequently, destructing the first component, in our case [f a],
    will only affect the right-hand side of the equality, and we will
    indeed get the desired equality [f a = Some p].
    As it can be seen below it works perfectly, and Coq is even able to
    prove the call is terminating on its own leaving us no obligations
    to fill.
*)

#[tactic="idtac"] Equations? f_sequence (a : A) : list A by wf a lt :=
  f_sequence a with inspect (f a) := {
    | Some p eqn: eq1 => p :: f_sequence p;
    | None eqn:_ => List.nil
    }.
Proof.
  apply decr_f. assumption.
Qed.

End Inspect.


(** 3.2 Improving recursion hypotheses

    In some cases,  most particularly when using a size or measure,
    it can happen that when defining a function by well-founded recursion,
    we forget that [x] is a subterm of a larger term [Y],
    and then we get stuck proving that "[size x < size Y]".
    In this case, a possible solution is to define a custom function to "carry"
    the information that [x] is a subterm of [Y], so it is available when
    trying to prove it is well-founded.

    For an example, consider RoseTrees, trees with finite subtrees represented
    by the constructor [node : list RoseTree -> RoseTree.]
    Let's also define the usual size function on it, and an equality test on lists.
*)

Section EqIn.

Context {A : Type}.

Inductive RoseTree : Type :=
| leaf : A -> RoseTree
| node : list RoseTree -> RoseTree.

Equations sizeRT (t : RoseTree) : nat :=
sizeRT (leaf a) := 1;
sizeRT (node l) := 1 + list_sum (map sizeRT l).

Equations eqList {X} (l l' : list X) (eq : X -> X -> bool) : bool :=
eqList [] [] _ := true;
eqList (a::l) (a'::l') eq := andb (eq a a') (eqList l l' eq);
eqList _ _ _ := false.

(** For pedagogical purposes, having define an equality test on list, we would
    like to define an equality test on RoseTree using well-founded recursion.

    If we try to define the equality test naively as below, [Equations] generates
    the obligation [sizeRT l < 1 + list_sum (map sizeRT lt)] corresponding to
    the case where [lt := l :: _].
    This is obviously true, but we are stuck trying to prove it as we do not
    remember that [l] is in [lt]:
*)

Equations? eqRT (eq : A -> A -> bool) (t t': RoseTree) : bool by wf (sizeRT t) lt :=
eqRT eq (leaf a) (leaf a') := eq a a';
eqRT eq (node lt) (node lt') := eqList lt lt' (fun l l' => eqRT eq l l') ;
eqRT eq _ _ := false.
Proof.
    simp sizeRT.
    (* What to do know ? We have forgotten that x is in l,
      and hence that sizeRT l < 1 + list_sum (map sizeRT lt)  *)
Abort.

(** To go around this kind of issues, a general method is to strengthen the
    function that goes through the structure to remember that [x] in a subterm of [Y].
    In our case, it means strengthening [eqList] so that to remember that [l] is
    in [lt].
    To do so, we ask for the input of the equality test [eq] of [eqList]
    to additionally be in in [l], i.e. [eq : forall x : X, In x l -> X -> bool].
    This way, in the case (lt := l :: _) we remember [In l lt].
    Doing so, it is now possible to define [eqRT] by well-founded on the size:
*)

Equations eqList' {X} (l l' : list X) (eq : forall x : X, In x l -> X -> bool) : bool :=
eqList' [] [] _ := true;
eqList' (a::l) (a'::l') eq := andb (eq a _ a') (eqList' l l' (fun x Inl y => eq x _ y));
eqList' _ _ _ := false.

Definition list_sum_ine (x : nat) (l : list nat) : In x l -> x < 1 + list_sum l.
Admitted.

Equations? eqRT (eq : A -> A -> bool) (t t': RoseTree) : bool by wf (sizeRT t) lt :=
eqRT eq (leaf a) (leaf a') := eq a a';
eqRT eq (node lt) (node lt') := eqList' lt lt' (fun l Inl l' => eqRT eq l l') ;
eqRT eq _ _ := false.
Proof.
  simp sizeRT. apply list_sum_ine. apply in_map. assumption.
Qed.

End EqIn.
