(** * Tutorial Equations : Basic Definitions and Reasoning with Equations

  *** Summary
  [Equations] is a plugin for Coq that offers a powerful support
  for writing functions by dependent pattern matching, possibly using
  well-founded recursion and obligations.
  To help reason on programs, [Equations] also comes with its own set of
  tactics, and can automatically derive properties like no-confusion
  properties or subterm relations.

  In this tutorial, we introduce the basic features of [Equations], step by
  step through practical examples.

  In section 1, we explain how to define basic functions by dependent
  pattern matching using [Equations], and how [Equations] helps to reason about
  such functions.
  We then discuss [with] clauses and [where] clauses in section 2 and 3, two
  features that provide flexibility when writing functions by dependent
  pattern matching.


  *** Table of content

  - 1. Basic definitions and reasoning
    - 1.1 Defining functions by dependent pattern matching
    - 1.2 Reasoning with [Equations]
      - 1.2.1 Simplifying goals with [autorewrite]
      - 1.2.2 Proving properties by functional elimination with [funelim]
      - 1.2.3 Discharging trivial goals with [simp]
      - 1.2.4 Extending [autorewrite] and [simp]
  - 2. With clauses
  - 3. Where clauses

  *** Prerequisites

  Needed:
  - We assume a basic knowledge of Coq and of defining functions by recursion

  Installation:
  - Equations is available by default in the Coq Platform
  - Otherwise, it is available via opam under the name coq-equations

*)



(** ** 1. Basic definitions and reasoning

  Let us start by importing the package:
*)

From Equations Require Import Equations.

Axiom to_fill : forall A, A.
Arguments to_fill {_}.

(** *** 1.1 Defining functions by dependent pattern matching

    In its simplest form, [Equations] provides a practical interface to
    define functions on inductive types by pattern matching and recursion
    rather than using Fixpoint and match.
    As first examples, let us define basic functions on lists.
*)

Inductive list A : Type :=
  | nil  : list A
  | cons : A -> list A -> list A.

Arguments nil {_}.
Arguments cons {_} _ _.

(** To write a function [f : list A -> B] on lists or another a basic
      inductive type, it suffices to:
    - Begin your definition with "[Equations]" rather than "[Fixpoint]".
    - Specify how the function, [f], computes on each constructor, [cst x1 ... xn],
      by writing [f (cst x1 ... xn) := t] where [t] may contain [f] recursively.
    - Separate the different cases by semi-colon "[;]"
    - As usual finish you definition by a dot "[.]"

  For instance, we can define the functions [tail], [length] and [app] by:
*)

Equations tail {A} (l : list A) : list A :=
tail nil := nil;
tail (cons a l) := l.

Equations length {A} (l : list A) : nat :=
length nil := 0;
length (cons a l) := S (length l).

Equations app {A} (l l' : list A) : list A :=
app nil l' := l';
app (cons a l) l' :=  cons a (app l l').

Infix "++" := app (right associativity, at level 60).


(** [Equations] is compatible with usual facilities provided by Coq to write
    terms:
    - It is compatible with implicit arguments that as usual do not need to
      be written provided it can be inferred.
      For instance, above, we wrote [app nil l'] rather than [app (nil A) l']
      as [A] was declared as an implicit argument of [nil].
    - We can use underscores "_" for terms that we do not use, terms
      that Coq can infer on its own, but also to describe what to do in all
      remaining cases of our pattern matching.
      As [list] only has two constructors, it is not very useful here,
      but we can still see it works by defining a constant function:
*)

Equations cst_b {A B} (b : B) (l : list A) : B :=
cst_b b _ := b.

(** - We can use notations both in the pattern matching (on the left-hand
      side of "[:=]") or in the bodies of the function (on the right-hand side
      of "[:=]"). This provides an easy visual way to define functions.
      For instance, with the usual notations for lists, we can redefine
      [length] and [app] as:
*)

Notation "[]" := nil.
Notation "[ x ]" := (cons x nil).
Notation "x :: l" := (cons x l).

Equations length' {A} (l : list A) : nat :=
length' []     := 0;
length' (a::l) := S (length' l).

Equations app' {A} (l l' : list A) : list A :=
app' []     l' := l';
app' (a::l) l' := a :: (app' l l').

(** For the users that would prefer it, there is also an alternative syntax
    closer to the the one provided by the [Fixpoint] command and Coq's native pattern-matching.
    With this syntax, we have to start each clause with "[|]" and separate the
    different patterns in a clause by "[,]", but we no longer have to repeat
    the name of the function nor to put parenthesis or finish a line by "[;]".

    With this syntax, we can rewrite [length] and [app] as:
  *)

Equations length'' {A} (l : list A) : nat :=
  | []     := 0
  | (a::l) := S (length'' l).

Equations app'' {A} (l l' : list A) : list A :=
  | []    , l' := l'
  | (a::l), l' := a :: (app'' l l').

(** In this tutorial, we will keep to the first syntax but both can be
    used interchangeably.

    [Equations] enables us to pattern match on several different
    variables at the same time, for instance, to define a function [nth_option]
    getting the nth-element of a list and returning [None] otherwise.
*)

Equations nth_option {A} (n : nat) (l : list A) : option A :=
nth_option 0 []     := None ;
nth_option 0 (a::l) := Some a ;
nth_option (S n) []     := None ;
nth_option (S n) (a::l) := nth_option n l.

(** However, be careful that as for definitions using [Fixpoint], the order
    of matching matters: it produces terms that are pointwise propositionally
    equal but with different computation rules.
    For instance, if we pattern match on [l] first, we get a function
    [nth_option'] that is equal to [nth_option] but computes differently
    as it can been seen below:
*)

Equations nth_option' {A} (l : list A) (n : nat) : option A :=
nth_option' [] _ := None;
nth_option' (a::l) 0 := Some a;
nth_option' (a::l) (S n) := nth_option' l n.

Goal forall {A} (a:A) n, nth_option n (nil (A := A)) = nth_option' (nil (A := A)) n.
Proof.
  (* Here [autorewrite with f] is a simplification tactic of [Equations] (c.f. 1.1.2).
     As we can see, [nth_option'] reduces on [ [] ] to [None] but not [nth_option]. *)
  intros.
  autorewrite with nth_option.
  autorewrite with nth_option'.
  (* We need to further destruct n to simplify *)
  destruct n; reflexivity.
Abort.

(** [Equations] also supports nested pattern matching.
    For instance, we can define a function swapping lists of pairs
    by matching the list and the pairs inside of it at the same time.
*)

Equations swap_list_pair {A B} (l : list (A * B)) : list (B * A) :=
swap_list_pair [] := [];
swap_list_pair ((a , b)::l) := (b,a)::(swap_list_pair l).

(** As exercises, you can try to define:
    - A function [map f l] that applies [f] pointwise, on [ [a1, ... ,an] ] it
      returns [ [f a1, ... , f an] ]
    - A function [head_option] that returns the head of a list and [None] otherwise
    - A function [fold_right f b l] that on a list [ [a1, ..., an] ]
      returns the element [f a1 (... (f an b))]
*)

Equations map {A B} (f : A -> B) (l : list A) : list B :=
map f _ := to_fill.

Equations head_option {A} (l : list A) : option A :=
head_option _ := to_fill.

Equations fold_right {A B} (f : A -> B -> B) (b : B) (l : list A) : B :=
fold_right f b _ := to_fill.

(* You can uncomment the following tests to try your functions *)
(*
Succeed Example testing : map (Nat.add 1) (1::2::3::4::nil) = (2::3::4::5::nil)
  := eq_refl.
Succeed Example testing : @head_option nat nil = None := eq_refl.
Succeed Example testing : head_option (1::2::3::nil) = Some 1 := eq_refl.
Succeed Example testing : fold_right Nat.mul 1 (1::2::3::4::nil) = 24 := eq_refl.
*)


(** *** 1.2 Reasoning with Equations  *)

(** Now that we have seen how to define basic functions, we need to
    understand how to reason about them.

    *** 1.2.1 Simplifying goals

    By default, functions defined using [Equations] are opaque and cannot
    be unfolded with [unfold] nor simplified with [simpl] or [cbn] as one
    would do with a [Fixpoint] definition.
    This is on purpose to prevent uncontrolled unfolding which can easily
    happen, particularly when doing well-founded recursion or reasoning
    about proof carrying functions.
    Yet this does not prevent us from using reflexivity when both sides
    of an equation are definitionally equal.

    For instance, consider [nil_app] the usual computation rule for [app].
    It cannot be unfolded, nor simplified by [cbn] but can be proven by
    [reflexivity].
*)

Lemma nil_app {A} (l : list A) : [] ++ l = l.
Proof.
  (* [unfold] fails, and [cbn] has no effect *)
  Fail unfold "++". Fail progress cbn.
  (* But [reflexivity] works *)
  reflexivity.
Qed.

(** If one really wishes to recover unfolding, it is possible to enable it 
    on a case by case basis using the option [Global Transparent f] as shown 
    below. It is also possible to set this option globally with [Set Equations
    Transparent], but it is not recommended to casual users.
    To recover simplification by [simpl] and [cbn], one can additionally
    use the command [Arguments function_name !_ /. ].
    It will simplify the function as soon as it is applied to at least one
    argument that is a constructor.
*)

Equations f4 (n : nat) : nat :=
f4 _ := 4.

Global Transparent f4.

Goal f4 3 = 4.
Proof.
  (* [f4] can now be unfolded *)
  unfold f4.
Abort.

Goal f4 3 = 4.
Proof.
  (* Yet, it still cannot be simplify by [cbn] *)
  Fail progress cbn.
  (* [Arguments] enables to recover simplification *)
  Arguments f4 !_ /. cbn.
Abort.

(** How does [Equations] work without [cbn] and [simpl]? Internally, [Equations]
    proves an equality for each case of the pattern matches and stores them
    in a hint database with the same name as the function. For the [app]
    function we defined, [Equations] declared and proved [app [] l' = l'] and
    [app (a::l) l' = a :: (app l l')] and stored them in the hint database
    [app].
    The equalities are named using the scheme "function_name_equation_n".
    You can check them out using the command [Print Rewrite HintDb function_name]:
 *)

Print Rewrite HintDb app.

(** It is then possible to simplify expressions with the functions [f1 ... fn]
    by using the tactic [autorewrite with f1 ... fn].
    Note, it is also possible to simplify in hypotheses using
    [autorewrite with f1 ... fn in H].

    As an example, let us prove [app_nil l : l ++ [] = l].
    As [app] is defined by pattern match on [l], we prove the result by
    induction on [l], and use [autorewrite with app] to simplify the goals.
*)

Lemma app_nil {A} (l : list A) : l ++ [] = l.
Proof.
  intros; induction l. all: autorewrite with app.
  - reflexivity.
  - rewrite IHl. reflexivity.
Qed.

Lemma app_assoc {A} (l1 l2 l3 : list A) : (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  induction l1. all: autorewrite with app.
  - reflexivity.
  - rewrite IHl1. reflexivity.
Qed.

(** This provides a fine control of unfolding as it simplifies only by the defined
    equations, and will not unfold anything else, while giving the option to
    rewrite directly by a specific equation.
    In particular, compared to [cbn] it will never unfold unwanted terms, like
    proof terms that would be part of the definition, for instance, when defining
    proof carrying functions or defining functions by well-fouded recursion.
*)

(** *** 1.2.2 Proving properties by functional elimination

    In the examples above, [app_nil] and [app_assoc], we mimicked the pattern
    used in the definition of [app] by [induction l].
    While it works on simple examples, it quickly gets more complicated.
    For instance, consider the barely more elaborate example proving
    that both definitions of [nth_option] are equal.
    We have to be careful to first revert [n] in order to generalise the
    induction hypotheses and get something strong enough when inducting on [l],
    and we then need to destruct n.
*)

Lemma nth_eq {A} (l : list A) (n : nat) : nth_option n l = nth_option' l n.
Proof.
  revert n; induction l; intro n; destruct n.
  all : autorewrite with nth_option nth_option'.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply IHl.
Abort.

(** On real life examples, reproducing the patterns by hand with the good
    induction hypotheses can quickly get tedious, if not challenging.
    Inductive types and patterns can quickly get complicated.
    Moreover, functions may actually not even be defined following the
    structure of an inductive type making it hard to reproduce at all.

    For a simple example, consider the function [half] and [mod2] that
    are defined recursively on [S (S n)] rather than on [S n]:
*)

Equations half (n : nat) : nat :=
half 0 := 0 ;
half 1 := 0 ;
half (S (S n)) := S (half n).

Equations mod2 (n : nat) : nat :=
mod2 0 := 0;
mod2 1 := 1;
mod2 (S (S n)) := mod2 n.

(** If we try to naively prove a property [P] about [half] or [mod2]
    by repeated induction on [n], we actually quickly get stuck.
    Indeed, as we can see below, in the recursive case we have to prove
    [P (S (S n))] knowing [P (S n)] and that [P n -> P (S n)].
    Yet, in general to be able to reason about [half] or [mod2],
    we actually need to know that [P n] hold to prove [P (S (S n))].
*)

Goal forall (P : nat -> Prop) (H0 : P 0) (H1 : P 1) (n : nat), P n.
Proof.
  induction n. 1: exact H0.
  induction n. 1: exact H1.
  (* We are stuck *)
Abort.

(** This issue arises more generally as soon as we start defining functions using
    more advanced notions of matching like [with] and [where] clauses (c.f. 2. and 3.),
    or when defining functions using well-founded recursion.

    Consequently, to help us reason about complex functions, for each definition,
    [Equations] derives a functional induction principle.
    This is an induction principle that follows the structure of the
    function, including nested pattern-matching, [with] and [where] clauses,
    correct induction hypotheses and generalisation as in the above example.
    This principle is named using the scheme "function_name_elim".

    For instance, to prove a goal [P] depending on [n] and [half n],
    [half_elim] asserts that it suffices to prove
    - [P 0 (half 0)]
    - [P 1 (half 1)]
    - and that [P n (half n) -> P (S (S n)) (half (S (S n)))]
    that is, exactly the pattern we wanted.
*)

Check half_elim.

(** Moreover, [Equations] comes with a powerful tactic, [funelim], that
    applies the functional induction principle and simplifies the associated definition.
    To use it, it suffices to write [funelim (function_name a1 ... an)]
    where [a1 ... an] are the arguments you want to do your induction on.

    As an example, let us prove [nth_eq] and [half_mod2] for
    which we can already see the advantages over trying to reproduce the
    pattern matching by hand:
*)

Lemma nth_eq {A} (l : list A) (n : nat) : nth_option n l = nth_option' l n.
Proof.
  funelim (nth_option n l).
  all: autorewrite with nth_option'.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply H.
Abort.

(* Doing induction naively to reproduce a pattern can get you stuck *)
Definition half_mod2 (n : nat) : n = half n + half n + mod2 n.
Proof.
  induction n. 1: reflexivity.
  induction n. 1: reflexivity.
  (* We simplify the goal *)
  autorewrite with half mod2.
  rewrite PeanoNat.Nat.add_succ_r. cbn.
  f_equal. f_equal.
  (* We then get stuck as we have the wrong hypotheses *)
Abort.

(* Wheras funelim does it automatically for you *)
Definition half_mod2 (n : nat) : n = half n + half n + mod2 n.
Proof.
  funelim (half n). 1-2: reflexivity.
  autorewrite with half mod2.
  rewrite PeanoNat.Nat.add_succ_r. cbn.
  f_equal. f_equal.
  (* We now have the good recursion hypotheses *)
  assumption.
Qed.

(** *** 1.2.3 Discharging trivial goals with [simp]

    In practice, it often happens in proofs by functional induction that after
    simplification we get a lot of uninteresting cases that we would like to
    deal with in an automatic but controlled way.
    To help us, [Equations] provides a tactic [simp f1 ... fn]
    that first simplify the goal by [autorewrite with f1 ... fn] then
    tries to solve the goal by a proof search by a particular instance of
    [try typeclasses eauto].
    It does so using the equations associated to [f1 ... fn], and the databases
    [Below] and [Subterm].

    Linking [simp] with [funelim] like [funelim sth ; simp f1 ... fn] then
    enables us to simplify all the goals and at the same to automatically
    prove uninteresting ones.
    For instance:
*)

Definition nth_eq {A} (l : list A) (n : nat) : nth_option n l = nth_option' l n.
Proof.
  funelim (nth_option n l); simp nth_option nth_option'.
  all : reflexivity.
Abort.

(** As you can see, by default [simp] does not try to prove goals that hold
    by definition, like [None = None].
    If you wish for [simp] to do so, or for [simp] to try any other tactic,
    you need to add it as a hint to one of the hint databases  used by [simp].
    In particular, you can extend [simp] to to prove definitional equality using
    the following command.
*)

#[local] Hint Resolve eq_refl : simp.

Definition nth_eq {A} (l : list A) (n : nat) : nth_option n l = nth_option' l n.
Proof.
  funelim (nth_option n l); simp nth_option nth_option'.
Qed.

(** *** 1.2.4 Extending [autorewrite] and [simp]

    By default, the tactic [autorewrite with f] only simplifies a term by the
    equations defining [f], like [[] ++ l = l] for [app].
    In practice, we may want to try other equations we have proved in our automatic
    simplification
    For instance, when reasoning on [app], we may want to further simplify
    by [app_nil : l ++ [] = l] or [app_assoc : (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)].
    We can extend [autorewrite] (and hence [simp]) to automatically apply our
    properties by adding them to the database associated to [f].
    This can be done with the following syntax:

      [ #[local] Hint Rewrite @lemma_name : function_name. ]

    This is a very powerful customizable rewrite mechanism.
    Actually, this mechanism is expressive enough to be non-terminating if the
    wrong lemmas are added to the database.
    Indeed, while it is confluent and terminating using only the defining
    equations, adding lemma like [add_comm : forall a b, a + b = b + a] will
    surely create a loop.

    To see how it can be useful, let us define a tail-recursive version of
    list reversal and prove it equal the usual one:
*)

Equations rev {A} (l : list A) : list A :=
rev [] := [];
rev (a::l) := rev l ++ [a].

Equations rev_acc {A} (l : list A) (acc : list A) : list A :=
rev_acc nil acc := acc;
rev_acc (cons a v) acc := rev_acc v (a :: acc).

Lemma rev_rev_acc {A} (l l' : list A) : rev_acc l l' = rev l ++ l'.
Proof.
  funelim (rev l). all: autorewrite with rev rev_acc app.
  - reflexivity.
  (* We have to rewrite by [app_assoc] by hand *)
  - rewrite app_assoc. apply H.
Abort.

(* Adding [app_nil] and [app_assoc] the database associated to [app] *)
#[local] Hint Rewrite @app_nil @app_assoc : app.

(* We can check it has indeed been added *)
Print Rewrite HintDb app.

(* [autorewrite with app] can now use [app_assoc] *)
Goal forall {A} (l1 l2 l3 l4 : list A),
     ((l1 ++ l2) ++ l3) ++ l4 = l1 ++ (l2 ++ (l3 ++ l4)).
Proof.
  intros. autorewrite with app. reflexivity.
Qed.

Lemma rev_eq {A} (l l' : list A) : rev_acc l l' = rev l ++ l'.
Proof.
  funelim (rev l);  autorewrite with rev rev_acc app.
  - reflexivity.
  (* There is no more need to call [app_assoc] by hand in proofs *)
  - apply H.
Abort.

(** It actually enables greatly automating proofs using [simp] *)
Lemma rev_eq {A} (l l' : list A) : rev_acc l l' = rev l ++ l'.
Proof.
  funelim (rev l); simp rev rev_acc app.
Qed.

(** *** Exercises *)

(** As exercises, you can try to prove the following properties  *)
Lemma app_length {A} (l l' : list A) : length (l ++ l') = length l + length l'.
Proof.
Admitted.

(* You will need to use the lemma [le_S_n] *)
Lemma nth_overflow {A} (n : nat) (l : list A) : length l <= n -> nth_option n l = None.
Proof.
Admitted.

(* You will need to use the lemma [PeanoNat.lt_S_n]
  HINT : [funelim] must be applied to the parameters you want to do the induction on.
         Here, it is [n] and [l], and not [n] and [l++l'].
*)
Lemma app_nth1 {A} (n : nat) (l l' : list A) :
      n < length l -> nth_option n (l++l') = nth_option n l.
Proof.
  (* intro H; funelim (nth_option n l); simp nth_option app.
  3: { apply H. apply PeanoNat.lt_S_n. } *)
Admitted.

(* You will need the lemma [le_S_n].
  HINT : [funelim] must be applied to the parameters you want to do the induction on.
         Here, it is [n] and [l], and not [(n - length l)] and [l']. *)
Lemma app_nth2 {A} (n : nat) (l l' : list A) :
      length l <= n -> nth_option n (l++l') = nth_option (n-length l) l'.
Proof.
Admitted.

Lemma distr_rev {A} (l l' : list A) : rev (l ++ l') = rev l' ++ rev l.
Proof.
Admitted.





(** ** 2. With clauses

    The structure of real programs is generally richer than a simple case tree
    on the original arguments.

    In the course of a computation, we might want to compute or scrutinize
    intermediate results (e.g. coming from function calls) to produce an answer.
    In terms of dependent pattern matching, this literally means adding a new
    pattern to the left of our equations made available for further refinement.
    This concept is know as [with] clauses in the dependently-typed programming
    community and was first introduced in the Epigram language.

    [With] clause are available in [Equations] with the following syntax
    where [b] is the term we wish to inspect, and [p1 ... pk] the patterns we
    match [b] to:

    [[
      f (cxt x1 ... xn) with b => {
        f (cxt x1 ... xn) p1 := ... ;
        ...
        f (cxt x1 ... xn) pk := ...
    }
    ]]

    As a first example, we can a define a function filtering a list by a
    predicate [p].
    In the case [cons a l], the [with] clause enables us to compute
    the intermediate value [p a] and to check whether it is [true] or [false],
    and hence if [a] satisfies the predicate [p] and should be kept or not:
*)

Equations filter {A} (l : list A) (p : A -> bool) : list A :=
filter nil p := nil ;
filter (cons a l) p with p a => {
  filter (cons a l) p true := a :: filter l p ;
  filter (cons a l) p false := filter l p }.


(** This syntax is a bit heavy. To avoid repeating the full clause
    [filter (cons a l) p] and to focus on the [with] pattern, we can use the
    [Fixpoint] like syntax in the with clause discussed in section 1.1.
    This enables to rewrite the [with] clause of the function [filter]
    much more concisely:
*)

Equations filter' {A} (l : list A) (p : A -> bool) : list A :=
filter' [] p => [];
filter' (a :: l) p with p a => {
  | true  => a :: filter' l p
  | false => filter' l p
  }.

(** To show that [filter] is well-behaved, we can define a predicate [In] and
    check that if an element is in the list and verifies the predicate,
    then it is in the filtered list.
*)

Equations In {A} (x : A) (l : list A) : Prop :=
In x [] => False ;
In x (a::l) => (x = a) \/ In x l.

(** For function defined using [with] clauses, [funelim] does the usual
    disjunction of cases for us, and additionally destructs the pattern
    associated to the [with] clause and remembers it.
    In the case of [filter], it means additionally destructing [p a] and
    remembering whether [p a = true] or [p a = false].

    For regular patterns, simplifying [filter] behaves as usual when using [funelim]:
*)

Lemma filter_In {A} (x : A) (l : list A) (p : A -> bool)
      : In x (filter l p) <-> In x l /\ p x = true.
Proof.
  funelim (filter l p); simp filter In.
  - intuition congruence.
  - rewrite H. intuition congruence.
  - rewrite H. intuition congruence.
Qed.

(** However, simplifying [with] clauses can make subclauses appear corresponding
    to the different branches of the [with] clause.
    For [filter'], in the [p a = true] case, a [filter_clause_1] appears, and
    similarly in the [false] case.
    This is due to [Equations]' internal mechanics.
    To simplify the goal further, it suffices to rewrite [p a] by its value
    in the branch, and to simplify [filter] again.
*)

Lemma filter_filter' {A} (l : list A) (p : A -> bool)
      : filter l p = filter' l p.
Proof.
  funelim (filter l p); simp filter'.
  - rewrite Heq. cbn. reflexivity.
  - rewrite Heq. cbn. reflexivity.
Qed.

(** [With] clauses can also be useful to inspect a recursive call.
    For instance, [with] clause enables us to write a particularly concise
    definition of the [unzip] function:
*)

Equations unzip {A B} (l : list (A * B)) : list A * list B :=
unzip [] := ([],[]);
unzip ((a,b)::l) with unzip l => {
  | (la,lb) => (a::la, b::lb)
}.

(** Finally, [with] clauses can be used to discard impossible branches.
    For instance, rather than returning an option type, we can define a
    [head] function by requiring the input to be different than the
    empty list.
    In the [nil] case, we can then destruct [pf eq_refl : False] which
    has no constructors to define our function.
*)

Equations head {A} (l : list A) (pf : l <> nil) : A :=
head [] pf with (pf eq_refl) := { };
head (a::l) _ := a.

(** As exercises, you can try to:
    - Prove that both head functions are equal up to [Some]
    - Prove that a filtered list has a smaller length than the original one
    - Define a function [find_dictionary] that given a key and an
      equality test, returns the first element associated to the key and
      [None] otherwise
*)

Definition head_head {A} (l : list A) (pf : l <> nil)
           : Some (head l pf) = head_option l.
Proof.
Admitted.

(* You may need the lemma le_n_S and PeanoNat.Nat.le_le_succ_r *)
Definition filter_length {A} (l : list A) (p : A -> bool)
           : length (filter l p) <= length l.
Proof.
Admitted.

Equations find_dictionary {A B} (eq : A -> A -> bool) (key : A)
          (l : list (A * B)) : option B :=
find_dictionary eq key [] := to_fill;
find_dictionary eq key _ with @to_fill bool => {
  | _ := to_fill
}.

(* You can uncomment the following tests to try your functions *)
(* Definition example_dictionnary :=
  (3,true::true::[]) :: (0,[]) :: (2,true::false::[]) :: (1,true::[]) :: [].
Succeed Example testing :
  find_dictionary Nat.eqb 2 example_dictionnary = Some (true::false::[]) := eq_refl.
Succeed Example testing :
  find_dictionary Nat.eqb 4 example_dictionnary = None := eq_refl. *)



(** ** 3. Where Clauses

    As discussed, we often need to compute intermediate terms,
    which is the purpose of the [with] clause.
    Similarly, we often need to define intermediate
    functions, for instance to make the code clearer or because a function
    needs to be generalised.

    This is the purpose of the [where] clause, that enables to define auxiliary
    function defined in the context of the main one.
    To define a function using a [where] clause, it suffices to start
    a new block after the main body starting with [where] and using
    [Equations]' usual syntax.
    Though be careful that, as it is defined in the context of the main
    body, it is not possible to reuse the same names.

    The most standard example is a tail-recursive implementation of list
    reversal using an accumulator.
    As an example, we reimplement it with a [where] clause rather than with an
    external definition.
*)

Equations rev_acc' {A} (l : list A) : list A :=
rev_acc' l := rev_acc_aux l []

where rev_acc_aux : (list A -> list A -> list A) :=
rev_acc_aux [] acc := acc;
rev_acc_aux (a::tl) acc := rev_acc_aux tl (a::acc).

(** Reasoning on functions defined using [where] clauses is a bit more tricky as we
    need a predicate for the first function, and for the auxiliary function. *)

Check rev_acc_elim.

(** The first one is usually called the wrapper and the other the worker.
    While the first one is obvious, as it is the property we are trying to prove,
    Coq cannot invent the second one on its own.
    Consequently, we cannot simply apply [funelim]. We need to manually apply
    the recurrence principle automatically generated by [Equations], [rev_acc_elim],
    ourselves.
*)

Lemma rev_acc_rev {A} (l : list A) : rev_acc' l = rev l.
Proof.
  unshelve eapply rev_acc'_elim.
  1: exact (fun A _ l acc aux_res => aux_res = rev l ++ acc).
  all: cbn; intros.
  (* Functional elimination provides us with the worker property initialised
    as in the definition of the main function *)
  - rewrite app_nil in H. assumption.
  (* For the worker proofs themselves, we use standard reasoning. *)
  - reflexivity.
  - simp rev. rewrite H. rewrite app_assoc. reflexivity.
Abort.

(** This proof can actually be mostly automated thanks to [Equations].
    - We can automatically deal with [app_nil] and [app_assoc] by adding
      them to simplification done by [autorewrite] as done in 1.1.2
    - We can combine that with a proof search using [simp]
    This enables to rewrite the proof to:
*)

Lemma rev_acc_rev {A} (l : list A) : rev_acc' l = rev l.
Proof.
  unshelve eapply rev_acc'_elim.
  1: exact (fun A _ l acc aux_res => aux_res = rev l ++ acc).
  all: cbn; intros; simp rev app in *.
Qed.
