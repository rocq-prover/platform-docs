(** * Inductive types and pattern matching

    *** Main contributors

    Patrick Nicodemus.

    *** Prerequisites

    The user is expected to be familiar with variants and pattern matching
    in a statically typed language such as OCaml, Haskell or Rust.
*)


(** ** 1. Basics

    In this section we explain the basics of inductive types and pattern
    matching in Rocq. We focus on the fragment of the language which
    Rocq shares with languages based on the Hindley-Milner type system
    with algebraic data types, such as OCaml and Haskell,
    deferring dependent types to the next section.

    Programmers who are experienced in OCaml or Haskell
    can skim this section quickly to learn the Rocq syntax
    for pattern matching and recursive function definitions via the
    [fix] combinator.

    Rocq allows the user to define inductive types, and define
    functions on them by pattern matching. Examples of inductive types
    include enumerated data types (or "enums") such as Booleans or
    the days of the week, algebraic data types
    such as linked lists and binary trees, and record types.

    Several inductive types
    are defined in Corelib.Init.Datatypes.v, and we will
    use these as our basic examples.
*)

Notation "x -> y" := (forall _ : x, y) (at level 99, right associativity, y at level 200).
Inductive bool : Set :=
| true : bool
| false : bool.

(** This illustrates the basic syntax: the user introduces a name for the type,
    and can optionally declare the sort that it belongs to.
    The user declares *constructors* of the type, which are new fresh
    constants of the language which belong to that type, or are
    functions which have that type as their codomain. This may remind you of
    what other languages call enumerated types or "enums"; indeed, an
    enum is a special case of an inductive type.

    Inductive types have two associated language constructs for defining
    expressions, pattern matching and fixpoint combinators. Pattern
    matching allows the programmer to do case analysis on a value
    of an inductive type, asking which of the constructors it comes from,
    similar to how the "case" statement 
 *)

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

(** The body of the negb function is a expression that evaluates to a value by
    matching the term b with the constructors on the left hand side of the
    arrow. Once b successfully matches with a constructor, the expression on the
    right hand side is returned: if [b] is [true], then the expression evaluates
    to [false], and if [b] is [false] then the expression evaluates to [true].

    Pattern matches can be freely nested in each other and other pattern matches:
 *)

Definition andb (a : bool) (b : bool) : bool :=
  match a with
  | true => match b with
           | true => true
           | false => false
           end
  | false => false
  end.

(** The following syntax sugar abbreviates nested pattern matching on a, then b: *)
Definition andb1 (a : bool) (b : bool) : bool :=
  match a, b with
  | true, true => true
  | true, false => false
  | false, true => false
  | false, false => false
  end.

(** As in OCaml and Haskell, we can use "wildcards" to indicate
    that any term should successfully match with this branch,
    if previous matches fail.
 *)
Definition andb2 (a : bool) (b : bool) : bool :=
  match a, b with
  | true, true => true
  | _, _ => false
  end.

(** The Corelib also defines a [unit] type with one constructor, and
    an [Empty_set] with no constructors.
    Vertical bars are not necessary when there are zero or one
    constructors.
*)

Inductive unit : Set :=
  tt : unit.

Inductive Empty_set : Set := .

(** [Empty_set] has the curious property that, because it has
    no constructors, to pattern match on it we require no branches.
 *)

Definition to_A (x : Empty_set) (A : Type) : A := 
  match x with
  end.

(** The examples we have considered so far are "enumerated types",
    where the constructors for the inductive type [T] have been constants
    inhabiting T. In the following example, we show that the programmer
    can declare constructors which are functions from another type into [T].
    We also illustrate that inductive types, like other kinds of definitions,
    can be *parameterized* by arguments, which defines a *family* of inductive
    data types. *)

Inductive option (A : Type) :=
| Some : A -> option A
| None : option A.

Arguments Some {A}.
Arguments None {A}.

(** We can construct elements of the type by applying the constructors
    to arguments.
*)
Check Some true : option bool.
Check Some false : option bool.
Check None : option bool.

(** All elements of the type [option A] are of the form [Some a], for [a : A],
    or [None]. The pattern matching rules for [option A] are in accordance
    with this principle: to define a function [f: option A -> X],
    one must specify where [f] sends elements of the form [Some a]
    (and in this case, the answer is allowed to depend on [a]) and
    where it sends the element [None].
 *)

Definition get_some_or_default (A : Type) (default: A) (p : option A) :=
  match p with
  | Some a => a
  | None => default
  end.

(** Note that in the first branch of the pattern match, we introduce a fresh
    variable [a], which is in scope on the right hand side of the arrow for that
    branch, permitting the value returned by the expression to depend on [a].
    This is one aspect that makes inductive types more powerful than enumerated
    types: constructors can be thought of as wrappers around their arguments,
    and in the pattern match one can branch on the wrapper and then return a
    value which is a function of the arguments in that wrapper.

    The arguments to a constructor for an inductive type don't have to be
    from a distinct type, they can be values of the inductive type
    currently being defined.
 *)

Inductive nat :=
| O : nat
| S : nat -> nat.

(** This definition introduces a new type constant [nat] and two new constants
    [S : nat -> nat] and [O : nat]. We can build other elements of [nat] by
    iteratively applying [S] to [O].
 *)

Check S (S (S (S O))) : nat.

(** Every element of [nat] is of the form [O] or [S n], where [n] is
    an element of [nat], so to define a function [nat -> X] it suffices
    to define it in these two cases. As before, in the successor case [S n]
    the expression on the right hand side of the [=>] is permitted to
    depend on [n].
 *)

Definition pred (m : nat) : nat :=
  match m with
  | O => O
  | S x => x
  end.

(** For "properly" inductive types, where the constructors for the type
    depend on elements of that type, it is possible to
    define functions by recursion. We introduce a new language construct,
    the fixpoint combinator.
    In Rocq, recursive functions must be
    named, so that they can call themselves recurively by name;
    one cannot have a recursive anonymous function defined using
    the syntax [fun x => t].

 *)

Definition addr (n : nat) : forall m : nat, nat :=
  fix add_rec (m : nat) {struct m} :=
    match m with
    | O => n
    | S m0 => S (add_rec m0)
    end.

(** Let's discuss this syntax in some detail. [addr] takes a
    natural number [n] and defines a function [nat -> nat],
    which is exactly the function (fun m => m + n), defined by
    recursion on [m]. The keyword [fix] is followed by the name
    of the recursive function being defined, here [add_rec];
    this name is only in scope within the definition of [add_rec],
    so that [add_rec] can recursively call itself. After
    the name [add_rec], the function takes a list of its arguments
    with their declared types. Last, we have the mysterious syntax
    [{struct m}], which is an abbreviation for
    "structural recursion on [m]"; a recursive function can take
    multiple arguments, but it always must have one distinguished
    argument, belonging to an inductive type, such that
    the function is "structurally decreasing" on that argument -
    here, since [add_rec] is structurally decreasing on [m],
    the function [add_rec] is only permitted to recursively call itself
    within the branches of the case analysis on [m]. This guard
    condition ensures that recursive functions eventually terminate.

    The programmer rarely has to write [{struct m}] explicitly, as
    Rocq can usually infer it, but it is likely to appear in Rocq's
    output when they are printing proof terms that use induction.
    Being aware of the meaning of this annotation
    can make the fully elaborated
    Gallina code look less intimidating.

    Programmers rarely use the [fix] keyword in the form given above.
    Instead, they use a vernacular command, [Fixpoint], which
    is very similar to [Definition] except that the function being
    defined is allowed to call itself recursively. Terms using
    written [Fixpoint] are transformed under the hood into
    terms using [fix]. Note that this code is more concise
    because the programmer doesn't have to introduce the local name
    [add_rec].
 *)

Fixpoint add (n m : nat) :=
  match n with
  | O => m
  | S n0 => S (add n0 m)
  end.

(** The inductive type of lists brings together two features we've seen,
    polymorphism in a type parameter and induction. *)
Inductive list (A : Type) :=
| nil : list A
| cons (head : A) (tail : list A) : list A.

Arguments cons {A}.
Arguments nil {A}.

(** This example is similar to the addition example.
    [fix f x y := t] is has a similar meaning to
    [let rec f x y = t in f] in ML, and [{struct l}]
    is a hint to he Rocq typechecker that this definition
    is by structural recursion on the variable [l],
    i.e., that the function is decreasing in [l],
    with [l] getting smaller in every recursive function call.
    You do not have to include the {struct l} annotation when
    programming, because Rocq can infer it, but it will
    appear in error messages while debugging, and it is helpful
    to be able to read it.
*)
Definition length (A : Type) : list A -> nat :=
  fix length_rec (l : list A) {struct l} :=
    match l with
    | nil => O
    | cons head tail => S (length_rec tail)
    end.

Definition concatenate (A : Type) : list A -> list A -> list A :=
  fix concat_rec (l1 : list A) (l2 : list A) {struct l1} :=
    match l1 with
    | nil => l2
    | cons head tail => cons head (concat_rec tail l2)
    end.

(** ** 2. Indices

    So far, we have seen how to define inductive types such as [bool]
    and [nat], and families of inductive types such as [option] and [list]
    parameterized by a type parameter. In this section we discuss
    *inductive families* of types, called *indexed inductive types*,
    which are distinguished from families
    of inductive types by the following subtlety: an inductive
    family of types [X : I -> Type] may have constructors
    whose arguments draw from the types [X i0], [X i1], [X i2],
    and whose return type may be of type [X j], where all the indices
    [i0,...,in, j] may be distinct. For an indexed inductive type, then,
    all of the types [X i] are simultaneously defined by a mutual recursion.

    We illustrate this by defining an indexed inductive with two
    types, defined by mutual recursion.
 *)

Inductive EvenOdd : bool -> Type :=
| ZeroEven : EvenOdd true
| S_EO : forall (b : bool), EvenOdd b -> EvenOdd (negb b).
  
(** [EvenOdd true] is the set of even natural numbers,
    and [EvenOdd false] is the set of odd natural numbers, but these
    sets are defined together rather than separately: one
    defines an even number to be either zero or the successor of an odd
    number, and an odd number to be the successor of an even number.
    It makes no sense to say here that
    "[EvenOdd true] is freely generated by its constructors",
    because [EvenOdd true] is not generated by constructors
    applied to elements of [EvenOdd true], but [EvenOdd false]
    as well. It is not the types [EvenOdd true] and [EvenOdd false]
    which are inductively defined, but the family of types [EvenOdd].
 *)

(** In the following inductive type definition, [vector] has one *parameter*,
    the type variable [A], which is "constant" for the sake of the inductive
    type definition; it also has an *index*, which is a natural number.
    The first line should be read as saying that for each type [A],
    [vector A] is an inductive family of types [nat -> Type],
    where a constructor may take an argument of type [vector A i]
    and return an argument of type [vector A j] for some i ≠ j.
 *)

Inductive vector (A : Type) : nat -> Type :=
| vnil : vector A O
| vcons : forall n : nat, A -> vector A n -> vector A (S n).

(** It has two constructors: [vnil], which is an element of the type [vector A 0];
    and [vcons], which is a function [vector A n -> vector A (S n)] for all [n].
    To define a function on the type of vectors,
    it suffices to define it on the constructors. *)

Arguments vnil {A}.
Arguments vcons {A} {n} head tail.

(** This function can be seen as a "verified" version of the concat
    function we defined earlier. The fact that this definition
    type-checks means that Rocq has guaranteed that indeed the
    concatenation of a list of length [n] with a list of length [m] is of
    length [n + m]. *)
Definition vconcat (A : Type) {n : nat} (l1 : vector A n) {m : nat} (l2 : vector A m
  ) : vector A (add n m) :=
  (** The type signature above is easy to read and reflects how we might
      want to use it, but giving every argument a name
      (fixing some specific [n] and [l1], as we did)
      is not really a good fit for defining
      functions by recursion. The fixpoint operator [fix] is used to define a
      function quantified over _all_ its inputs, not just the specific ones
      given to us; 
      so we're just going to define this function for _all_
      [n'] and [l1'], and then apply it to the specific [n] and [l1] given to us.
      I introduce new variable names in defining [vconcat_rec]
      to avoid confusion;
      you could reuse the same names, but it would just shadow the outer names.
  *)
(fix vconcat_rec {n'} (l1' : vector A n') : vector A (add n' m) :=
     match l1' with
     | vnil => l2
     | vcons head tail => vcons head (vconcat_rec tail)
     end) n l1.
(** In the example above, if you remove [: vector A (n' + m)], it
    won't compile. Rocq is unable to infer the return type unless it is
    explicitly annotated. As a general rule, if your code doesn't
    compile, adding more type annotations and filling in implicit
    arguments may help you get better error messages, and make the
    typechecker happy, _up to a point_.

    However, if you don't understand how to correctly communicate type
    annotations to the compiler, then all your efforts will be in
    vain, which is why it's so important to understand how to read and
    write dependent pattern matching type annotations in Rocq.

    Thus, we turn to the details of dependent pattern matching.
    *)

(** ** 3. Dependently typed pattern matching

    In this section, we will front-load most of the theory,
    so if you get overwhelmed, skip ahead to the worked examples.
 
    The type of natural numbers [nat] that we defined earlier
    can be defined in language with algebraic data types
    like OCaml or Haskell. However, even though the type itself
    may seem fairly simple, the pattern matching rule for
    for defining functions on the natural numbers must account for
    dependent typing: the elimination rule does not just tell us how to
    define a function [nat -> A], but how to define an element of
    [forall n: nat, P] where [P] may depend nontrivially on [n].

    Because [P] can depend on [n], the appropriate
    return type of the match statement
    will thus vary in each branch of the match statement. We thus
    extend pattern matching with additional syntax which shows how
    the return type depends on the term being matched (the "discriminee").

    The full syntax for pattern matching on natural numbers is:
<<<

   match p as t return K with
   | O => e1
   | S x => e2

>>>

    where [p] is any term of type [nat], [t] is a new variable of type [nat],
    [K] is a type expression depending on [t], and [e1,e2] are terms
    (where [e2] is allowed to depend on the variable [x]).

    The rules for type-checking this expression are:
    1. [p] should be of type [nat]
    2. [K] should be a well-typed sort
    3. [e1] should be of type [K[t/O]]
    4. [e2] should be of type [K[t/S x]]

    and if all these are satisfied, then the whole match expression is
    of type [K[t/p]].

    We do an example.    
 *)

Definition nat_induction (P : nat -> Type) (x0 : P O) (Ps : forall (n : nat), P n -> P (S n))
  : forall (n : nat), P n
  := (fix nat_rec (n : nat) : P n :=
    match n as t return P t with
    | O => x0
    | S x => Ps x (nat_rec x)
    end).

(** Ignoring the novel syntax for a moment, we discuss the proof.
    We want to prove [forall n, P n], so we recurse on [n]. In the case where
    [n] is [O], we supply the assumed proof [x0] of [P 0]; otherwise,
    if [n] is a successor [S x], we recursively apply [nat_rec] to [x]
    to get a proof of [P x], and then apply Ps to this proof.

    There is something subtle happening here: in the first branch of the match 
    statement, we return [x0], which is assumed to be a proof of [P O],
    but as indicated in the type annotation for [nat_rec], the return type
    should be [P n]. Thus, the fact that this pattern match is well-typed
    relies on a crucial piece of reasoning, that in the first branch of
    the pattern match, since [n] is specialized to [O], the return type
    [P n] can also be specialized to [P O].

    This is what motivates the novel syntax [as t return P t].
    Here, [t] is a new variable that is bound in the type [P t]
    described after the [return] keyword; the return type of the expression
    is given by substituting in the discriminee [n] for [t] in [P t],
    in this case, [P n]. This annotation allows us to specify how the
    return type should be specialized within each branch of the match statement:
    in the first branch, [t:=O],
    and Rocq expects that branch to return a value of type [P O];
    in the second branch, [t:=S x], so Rocq expects the branch to
    return a value of type [P (S x)].

    More generally, in a pattern match
    [match s as t return K | c0 a1 a2 a3 => e0 | c1 b1 b2 => e1 | (...) end],
    where [s] is any term, [t] is a new variable, and [K] is an
    type depending on [t], Rocq will check that in the first branch,
    [e0] is of type [K[t/(c0 a1 a2 a3)]], in the second branch
    [e1] is of type [K[t/(c1 b1 b2)]], and so on.

    In this case the annotation [as t return P t] is unnecessary,
    because Rocq can figure this out. But for more complex
    examples it may fail to infer the type.
 *)

(** For indexed inductive types, there is one more point of complexity that
    needs to be addressed for dependent elimination. Because the constructors of
    an indexed inductive type can go between types in the family, within a given
    branch of a pattern match, the indices, too, become specialized to take on
    more concrete values, and so to the extent that the return type
    is dependent upon on the indices, that information needs to be
    taken into account in that branch of the pattern match. So, we extend
    the syntax one more time for this.

    Let's give an example.
 *)

Inductive is_even : nat -> Prop :=
| z_is_even : is_even O
| ss_is_even : forall n : nat, is_even n -> is_even (S (S n)).

(** The [is_even] family of types is a predicate on the natural
    numbers. To prove that a number [n] is even, we construct an inhabitant 
    of the [Prop] [is_even n].

    We want to prove that the sum of two even
    numbers is even. First, examine the structure of this proof leading up
    to the match statement to make sure you understand the context.
    The annotated type of the [fix] states that the [match]
    should return an element of type [is_even (add n m)].
    
    Consider the first branch of the pattern match. Because
    [z_is_even : is_even O], if [p] is [z_is_even],
    then since [p : is_even n] by assumption, we must have [n = O] in that
    branch. This makes returning [q] from that branch well-typed, because
    [q : is_even m] and the return type required by the [fix] annotation
    is [is_even (add n m)], which is [is_even m] when [n=O]. But
    we must have some way of telling Rocq the way in which the output
    type of the match depends on the indices of the discriminee,
    which is our motivation for the syntax
    [in is_even a return is_even (a + m)].
    Here, [a] is a fresh variable introduced to name the index of [p],
    where [a] is bound in [is_even (a + m)].
 *)

Definition sum_even:
  forall n m : nat, is_even n -> is_even m -> is_even (add n m) :=
  fix sum_even_rec (n m : nat) (p : is_even n) (q : is_even m) : is_even (add n m)
    :=
    match p in is_even a return is_even (add a m) with
    | z_is_even => (* 1 *) q 
    | ss_is_even n' p' => (* 2 *) ss_is_even (add n' m) (sum_even_rec n' m p' q)
    end.

(** The variable [a] cannot be referred to anywhere outside the
    definition of the return type - its only purpose is to explain
    how the return type varies with each branch of the pattern match.

    [a] will take on different values as a result of the different
    branches. In the first branch, (after the [| z_is_zero => ] ),
    [a] becomes equal to [0].
    Thus, at [q] , the return type is
    [is_even (0 + m)].
    In the second branch, [a] becomes equal to [(S (S n'))] and
    thus the return type is
    [is_even (S (S n') + m)].

    We can confirm this by entering proof mode, putting holes
    to replace [q] and [ss_is_even (...)],
    and using [refine] to fill in everything but the holes.
    The interactive proof mode shows us what the type of each hole is.
    As you can see, it depends on the value of the variable [a]. 
 *)

From Stdlib Require Import Ltac.  
Goal forall n m : nat, is_even n -> is_even m -> is_even (add n m).
Proof.
  refine (fix sum_even_rec
            (n m : nat) (p : is_even n) (q : is_even m) : is_even (add n m)
          := match p in is_even a return is_even (add a m) with
             | z_is_even => _
             | ss_is_even n' p' => _
             end).
Abort.


(** Try the same trick here of looking at the return type using [refine]
   to see how the context and return type changes inside the branches
   [| tt => _ ] and [| ff => _ ]. *)
 
Definition bool_induction :
  forall P : bool -> Type,
    P true -> P false -> forall b : bool, P b :=
  fun P pf_tt pf_ff b =>
  match b as b' return P b' with
  | true => (* 1 *) pf_tt
  | false => (* 2 *) pf_ff
  end.

(** ** 4. Case study: Equality

    The propositional equality type is a relatively
    simple example of an indexed inductive type which allows us to
    work through some examples without too much additional complexity.
 *)

Inductive eq {A: Type} (a : A) : A -> Prop :=
  eq_refl : eq a a.

(** We don't have to prove reflexity, because it's baked into the definition,
    but the other basic properties of equality are an interesting exercise. *)

(** The proof for eq_sym
    is just like the other examples we've done with inductive types,
    there are no new principles at work here,
    although it takes some work to see the resemblance.
    It is the same basic rule of dependent pattern matching.*)

Definition eq_sym : forall (A : Type) (x y : A), eq x y -> eq y x :=
  (** We don't bother introducing names for [x] and [y] because
   we don't need them. *)
  fun A x _ eq_xy =>
    (** Because [eq] is an inductive type, we can only use it by
      pattern matching, it's the only thing we know how to do. *)
    (** The reason we didn't bother introducing a name for [y] above
        is because the only reason we care about the value of [x] and [y]
        is to specify the return type of the function -
        but the only variables you can use to specify the return type
        of the function are the ones you introduce using the [as] and [in]
        keywords.

        Notice that the first parameter in [eq _ z] is an underscore.
        This is because its value is uniquely determined by the argument
        eq_xy (it has to be x) and the *parameters*, unlike the
        *indices*, are "constant" throughout the induction, i.e.,
        they play no role in the recursion or pattern matching.
        For this reason Rocq refuses to let you put a value there,
        presumably to avoid confusion (it would have no effect, 
        because the point of the "in" block is to allow you to introduce
        variables to describe the way the return type depends on the indices;
        the return type doesn't vary as a function of the parameters.)

        The same is true of the underscore after eq_refl. The value
        in that hole is completely
        determined by eq_xy (it's x), it's not introducing a new
        variable that you can use in the return expression.
     *)
    match eq_xy in
          eq _ z   (** Since eq_xy : eq x y, z = y "outside" the match: *)
          return eq z x (** from the "outside", [eq z x] is [eq y x]. *)
    with
    | eq_refl _ =>
       (** At this branch of the match statement, the variable [z]
           takes on a more concrete, specialized values for this branch,
           corresponding to the constructor. By definition [eq_refl x : eq x x],
           so [z] becomes [x], and [eq z x] becomes [eq x x].
         Again you can see this by entering tactic mode and doing a [refine]
         with the proof at this point. This means we can return [refl x],
         which is of the correct type.
         *)
        eq_refl x
    end.

Definition eq_trans : forall (A : Type) (x y z : A), eq x y -> eq y z -> eq x z :=
  fun A x y z eq_xy eq_yz =>
    (** First we prove that [y = z -> x = z]. The return type
        of the match is eq y z -> eq x z, because y' is bound to y. *)
    (match eq_xy in eq _ y' return eq y' z -> eq x z with
     | eq_refl _ =>
         (** At this point in the code, [y'] is equal to [x],
       and we want to prove that [x = z -> x = z]. But this is trivial. *)
         (fun eq_xz => eq_xz)
     end)
        (** Then we apply this to [eq_yz]. *)
      eq_yz.

(** You can delete the type annotation
    [as _ in eq x' y' return eq y' z -> eq x' z]
    and Rocq will still accept it. The type annotations
    are helping us understand what Rocq is doing,
    and helping us debug when Rocq can't figure it out.
 *)

(** Theorem: Functions preserve equality. *)
Definition fmap : forall (A B : Type) (f : A -> B) (a a' : A),
    eq a a' -> eq (f a) (f a') :=
  fun A B f a _ eq_aa' =>
    match eq_aa' in eq _ y return eq (f a) (f y) with
    | eq_refl _ =>
        (** At this point in the code, [eq a y] becomes [eq a a];
           and we are trying to return a value of type [eq (f a) (f a)].
           But this is immediate by reflexivity. *)
        eq_refl (f a)
    end.

(** We end with a nontrivial theorem that requires a lemma,
    which we do using a let binding. *)
Import Logic.
Print True.
Definition true_is_not_false : eq true false -> False :=
  (** The proof of this goes by a standard trick. *)
  (** First, we define a family of dependent types on [bool],
     [P tt tt = True]
     [P ff tt = False]
     [P tt ff = False]
     [P ff ff = True]
   *)
  let P : bool -> bool -> Prop :=
    fun b1 b2 =>
      match b1, b2 with
      | true, true => True
      | false, true => False
      | true, false => False
      | false, false => True
      end
  in
  let lemma : (forall b1 b2 : bool, eq b1 b2 -> P b1 b2) :=
    fun b1 _ eq_b1_b2 =>
      (match eq_b1_b2 in eq _ b2 return P b1 b2 with
       | eq_refl _ => (** Return type of the function is now [P b1 b1] *)
          match b1 as b1' return P b1' b1' with
          | true => (** Return type of the function is now [P true true] *)
              I
          | false => (** Return type of the function is now [P false false] *)
              I
          end
      end)
  in
  (** Now that we've proven that [P b1 b2] has a section for all [p1 p2],
     we just apply it to the assumptions in the question.
   *)
  fun eq_tt_ff => lemma true false eq_tt_ff.

(** Again, all these type annotations are often not necessary,
    as Rocq can infer them from context.
    But adding more annotations can help you get better error messages.
    Once you get it to compile, you can try deleting the type
    annotations and see if it still compiles.
 *)
