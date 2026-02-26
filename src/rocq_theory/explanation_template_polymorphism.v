(** * Template vs. “full” universe polymorphism

    *** Main contributors

    Sébastien Michelland, Yannick Zakowski.

    *** Summary

    Universe polymorphism in Rocq is a thorny subject in general, in the sense
    that it's rather difficult to approach for non-experts. Part of it is due
    to the fact that Rocq hides most things universes by default. For jobs that
    don't need universe polymorphism, Rocq does the right thing basically all
    the time with no user input, which is fantastic. However, when universe
    polymorphism _is_ needed and you, as a user, need to get into it, the
    hidden mechanisms tend to work against you. So let's unpack that.

    Rocq provides two mechanisms to support universe polymorphism in a broad
    sense. The historically first mechanism implemented is named “template
    polymorphism”. Nowadays, “proper” universe polymorphism is also supported.
    Unfortunately, numerous definitions in the standard library, such as the
    product type, are defined as template polymorphic, which may lead to
    troubles: in this tutorial, we illustrate when and where things can go
    wrong.

    We'll first go through examples of monomorphic (i.e., fixed) universes to
    explain the initial problem. From there, showing what template universe
    polymorphism does and why it's not enough is actually fairly
    straightforward. This eventually leads to universe polymorphism as a more
    general solution.

    *** Contents

    - 1. Quick reminder about universes
    - 2. Some issues with monomorphic universes
    - 3. What template universe polymorphism does and doesn't do
      - 3.1. Principle
      - 3.2. Breaking cycles with template polymorphism
      - 3.3. Template polymorphism doesn't go through intermediate definitions
    - 4. A taste of “full” universe polymorphism
      - 4.1. Principle
      - 4.2. Universe polymorphic definitions

    *** Prerequisites

    Needed:
    - The reader should have a basic understanding of universes. There is a
      reminder below but not at all a complete explanation.

    Not needed:
    - Experience with universe polymorphism.

    Installation: No plugins or libraries required.
*)

(** ** 1. Quick reminder about universes

    A basic understanding of universes would be best to read this tutorial, but
    just in case here's a quick recap'.

    The reason for universes is that there is no obvious type that can be
    assigned to the term [Type]. You can decide not to give it a type (in which
    case the calculus has more or less two kinds, values and types, like in
    Haskell). But if you decide to give it one, as the Calculus of
    Constructions does, you cannot make it [Type] itself, because [Type: Type]
    leads to logical inconsistencies known as Girard's paradox. ([Check Type]
    might appear to say that, but there are universes hidden there that Rocq
    only prints if you ask for [Set Printing Universes], as we'll see.)

    The basic idea for universes is to organize types into a hierarchy. Usual
    datatypes such as natural numbers or strings have as type the bottom
    element in the hierarchy, [Type@{0}]. The type of [Type@{0}] is the next
    element [Type@{1}]; the type of [Type@{1}] is [Type@{2}], and so on, with
    the typing rule [Type@{i}: Type@{i+1}] (infinitely). The type-to-element
    relation is well-founded, which salvages consistency. The integer
    associated with each element of the hierarchy is called a _universe level_
    or _universe_ for short.

    In Rocq, [Type@{0}] is written [Set] for historical reasons. The word [Type]
    on its own doesn't refer to any particular universe level; instead, it
    means something closer to [Type@{_}] where Rocq infers a universe level
    based on context, which can be confusing. This is why any job that involves
    inspecting universes requires [Set Printing Universes], and why here we'll
    will write most universes explicitly.

    Beyond checking the types of sorts, universes above 0 appear as a result of
    quantification. As a naïve intuition, any term that quantifies over types
    lives in a universe higher than 0. For example, the sort of base values
    like [73] is [Type@{0}] since [73: nat: Type{0}]. However, the sort of a
    basic [list] type constructor [list] will be [Type@{1}], following the
    judgement [list: Type@{0} -> Type@{0}: Type@{1}].

    Rocq implements a rule called _cumulativity_ (which is independent from the
    CoC) which extends the judgement of universes to [Type@{i}: Type@{j}] for
    [i < j]. This makes it so that higher universes as essentially “larger”
    than lower universes, as if the lower universes were literally included in
    the higher ones.

    All of this results in the following basic rule: wherever a type in universe
    [Type@{j}] is expected, you can provide a type from any universe smaller
    than [j], i.e. that lives in [Type@{i}] with [i <= j]. This is the main
    criterion that one has to care about when testing and debugging universes.

    Let's see this in action by looking at a completely monomorphic definition
    of a product type, i.e., one that lives in a single fixed universe. As
    mentioned before, Rocq tries pretty hard to hide universes from you. One of
    the consequences is that we need [Set Printing Universes] to see anything
    we're doing. *)
Open Scope type_scope.
Set Printing Universes.

(** Let us create a variable [uprod] representing a universe level, and then
    the product of two types living in universe [uprod]. *)
Universe uprod.
Inductive mprod (A B: Type@{uprod}) := mpair (a: A) (b: B).

(** For simplicity we're using the same universe level for both A and B; this
    is irrelevant to the issues below. *)
About mprod.

(** uprod is a fixed universe, and so the basic rule applies: we can use it with
    any type that lives in a lower universe, but we can't use it with a type
    that lives in a higher universe. *)
Check (fun (T: Type@{uprod}) => mprod T T).
Fail Check (fun (T: Type@{uprod+1}) => mprod T T).

(** You might think that [uprod] has to be a specific concrete integer so that
    universe consistency checks can be performed during typing. However, we can
    satisfy CoC rules without assigning specific integers and keep universes
    like [uprod] symbolic as long as there _exists_ a concrete assignment that
    keeps things well-typed.

   Rocq uses these so-called “algebraic” universes: a universe number is either
   a symbol (e.g. [uprod]), the successor of a symbol (e.g. [uprod+1]), or the
   max of two levels (e.g. [max(uprod, uprod+1)]). Counter-intuitively, we
   actually cannot specify universes directly by numbers. *)

Check Type@{uprod}.
Check Type@{uprod+1}.
Check Type@{max(uprod, uprod+1)}.
(* Check Type@{10}. *)
(* Error: Syntax error: '_' '}' or [universe] expected after '@{' (in [sort]). *)

(** The operators [+1] and [max] arise from typing rules; the important part is
    that these are the only ones needed to implement all the rules. The calculus
    of integers with [+1], [max], [<=] and [<] is decidable and thus it's
    possible for Rocq to carry out universe consistency checks using these
    algebraic universes without assigning concrete numbers.

    Instead, when you use a term of type [Type@{i}] where a term of type
    [Type@{j}] is required, Rocq checks that the _constraint_ [i <= j] is
    realizable: if it is, the constraint is recorded and the term is well-typed;
    otherwise a universe inconsistency error is raised. *)

(** For instance if we instantiate mprod with a [Set], we get [Set <= uprod],
    because a type at level [uprod] was expected and we provided one at level
    [Set]. The constraint is realizable so the definition is accepted. *)
Check (mprod (nat: Set)).

(** If we instantiate with a Type at level 1, we get the stronger constraint
    [Set < uprod]. It's still realizable, so the definition typechecks again;
    however, all future definitions must be compatible with the constraint,
    otherwise there will be a universe inconsistency. *)
Check (fun (T: Type@{Set+1}) => mprod T).

(** What we have to accept now is that we're never getting a concrete value out
    of that universe [uprod]: it's always going to remain a variable, and it
    will only evolve in its relations with other universe variables, i.e.
    through constraints. *)

(** ** 2. Some issues with monomorphic universes *)

(** The core limitations of template universe polymorphism are related to when
    it doesn't activate and leaves you with monomorphic universes, so we can
    demonstrate most of the issues directly on monomorphic universes.

    Let's introduce a new universe [u]. Initially [u] and [uprod] are
    unrelated, which we can see by printing the section of the constraint graph
    that mentions these two universes. (Note that we don't care about the
    [Set < x] constraints; all global universes have it.) **)
Universe u.
Print Universes Subgraph (u uprod).

(** Now if we instantiate [mprod] with a [Type@{u}], we get a new constraint
    that [u <= uprod]. Note that this constraint is _global_, so it now affects
    typing for all remaining code! *)
Definition mprod_u (T: Type@{u}) := mprod T T.
Print Universes Subgraph (u uprod).

(** (This is one of the reasons why universes can be difficult to debug in Rocq:
    any _use_ of a definition might impact universe constraints, so importing
    certain combinations of modules, adding debug lemmas, or any other change in
    global scope can affect whether code ten files over typechecks.) *)

(** This constraint changes if we now try to use [mprod] with a [Type@{u+1}]. *)
Definition mprod_up1 (T: Type@{u+1}) := mprod T.
Print Universes Subgraph (u uprod).

(** This is a pretty artificial example, but as mentioned in the introduction
    universe bumps occur naturally due to quantification. For example, let's say
    we want a “lazy” value wrapper that stores values through unevaluated
    functions. *)
Inductive lazyT: Type -> Type :=
  | lazy {A: Type} (f: unit -> A): lazyT A.

(** [lazy] contains a universe bump: due to quantification, the types that we
    provide for [A] will have to live in strictly smaller universes than the
    associated [lazyT]. This is not required by the type itself... *)
About lazyT.
(* lazyT : Type@{lazyT.u0} -> Type@{max(Set,lazyT.u1+1)} *)

(** But it is required by the [lazy] function, which takes a [lazyT.u1], thus
    smaller than [lazyT] which lives at level [lazyT.u1+1]. *)
About lazy.
(* lazy : forall {A : Type@{lazyT.u1}}, (unit -> A) -> lazyT A *)

(** Note that the bump only exists because [lazy] quantifies on [A]. In this
    simple example, we could make [A] a parameter of the inductive instead of an
    index and avoid the bump, but it's not the case in general (e.g., the freer
    monad or functor laws). *)

(** We can see this in a universe constraint if we bring them both in a single
    definition, such as the very natural [lazy_pure] function below. A universe
    variable [lazy_pure.u0] is introduced for [A], and since we supply [A] as
    (implicit) argument to [lazy]'s [A] argument which lives in universe level
    [lazyT.u1], we get [lazy_pure.u0 <= lazyT.u1].

    Since [lazyT] itself lives at level [lazyT.u1+1], the new constraint
    [lazy_pure.u0 <= lazyT.u1] implies a strict inequality between the
    universes of [A] and [lazyT A]. *)
Definition lazy_pure {A: Type} (a: A): lazyT A := lazy (fun _ => a).
Print Universes Subgraph (lazy_pure.u0 lazyT.u0 lazyT.u1).

(** We run into the typical limitation of monomorphic universes if we now
   happen to want products in these two places at once:
   - Products as arguments to [lazyT] (enforcing [uprod <= lazyT.u1])
   - [lazyT] within products (enforcing [lazyT.u1+1 <= uprod]).
   This is a very common thing to want, especially when passing values around as
   products, which happens all the time. *)

(** Currently we don't have any constraint between [lazyT.u1] and [uprod]. *)
Print Universes Subgraph (lazyT.u1 uprod).

(** If we were now to use [mprod] in a [lazyT], we'd get [uprod <= lazyT.u1]. *)
Definition lazy_pure_mprod {A B: Type} (a: A) (b: B): lazyT (mprod A B) :=
  lazy_pure (mpair _ _ a b).
Print Universes Subgraph (lazyT.u1 uprod).

(** Conversely, if we used [lazyT] in [mprod], we'd get [lazyT.u1 < uprod].
    Because we've defined [lazy_pure_mprod], this is inconsistent with existing
    constraints, so the definition doesn't typecheck! *)
Fail Definition mprod_lazy {A B: Type} (a: A) (b: B):
    mprod (lazyT A) (lazyT B) :=
  mpair _ _ (lazy_pure a) (lazy_pure b).

(** This definition would have been accepted had we not defined
    [lazy_pure_mprod] just prior. In fact, we can have _either_ one of these
     definitions, but we can't have _both_. Which is typically how you get to
     errors appearing or disappearing based on what modules have been imported
      and in what order, a.k.a., everyone's favorite. *)

(** ** 3. What template universe polymorphism does and doesn't do *)

(** *** Principle *)

(** Template universe polymorphism is a middle-ground between monomorphic
    universes and proper polymorphic universes that allows for some degree of
    flexibility. We can see it mentioned in the description of [prod] from the
    standard library; [About] says "[prod] is template universe polymorphic on
    [prod.u0] [prod.u1]". This has no effect on the printed type, because it
    only affects instances. *)
About prod.

(** Now, remember how [mprod] lives at level [uprod] all the time? This shows if
    we instantiate it with any random type: we get [mprod T T: Type@{uprod}]. *)
Check (fun (T: Type) => mprod T T).

(** Now the same with the standard [prod] gives us a slightly different
    result. *)
Check (fun (T: Type) => T * T).

(** Ignoring the fact that prod has two separate universes for its arguments,
   the real difference is that [T * T] lives in the same universe as [T] (which
   is called [Type@{Top.N}] or [Type@{JsCoq.N}] for some [N], depending on the
   environment in which you're running this file), not in a fixed universe like
   [uprod]. We could also instantiate [prod] with propositions or sets and the
   resulting product would correspondingly live in [Prop] or [Set]. *)
Check (fun (P: Prop) => P * P).
Check (fun (S: Set) => S * S).

(** In other words, [prod] can live in different universes depending on what
    arguments it is applied to, making it “universe polymorphic” in a certain
    sense. You can think about it as being parameterized over universe levels,
    with the constraint that the input levels must be below [prod.u0] and
    [prod.u1] respectively. *)

(** *** Breaking cycles with template polymorphism *)

(** It looks like we've solved our universe problem now because we can have both
    definitions of [prod] within [lazyT] and [lazyT] within [prod]. *)
Definition lazy_pure_prod {A B: Type} (a: A) (b: B): lazyT (A * B) :=
  lazy_pure (pair a b).
Definition prod_lazy {A B: Type} (a: A) (b: B): lazyT A * lazyT B :=
  pair (lazy_pure a) (lazy_pure b).

(** The constraints are not gone: it's just that now the two instances of [prod]
    live in different universes:
    - In [lazy_pure_prod], [A] and [B] live in [lazy_pure_prod.u0] and
      [lazy_pure_prod.u1] respectively; [prod] lives in the max of both which
      must be lower than [lazyT.u1], meaning [lazy_pure_prod.{u0,u1} <=
      lazyT.u1].
    - In [prod_lazy], [lazyT A * lazyT B] is built out of two types in
      [lazyT.u1+1], meaning that [lazyT.u1 < prod.{u0,u1}]. *)
Print Universes Subgraph (
  lazyT.u1 prod.u0 prod.u1
  lazy_pure_prod.u0 lazy_pure_prod.u1
  prod_lazy.u0 prod_lazy.u1).

(** There are other constraints here but they're unrelated to the inconsistency
    that we had with the monomorphic version. *)

(** *** Template polymorphism doesn't go through intermediate definitions *)

(** And thus, the problem is solved... but only when the universe at fault
    comes from an inductive type directly (here, [prod]). Template polymorphic
    universes don't propagate to any other derived definition. So if we define
    the state monad for example, it will not itself be universe polymorphic at
    all, and thus it will exhibit the same behavior as [mprod]. *)
Definition state (S: Type) := fun (T: Type) => S -> (S * T).
About state.

(** [state.{u0,u1}] correspond to the old [uprod]: the type of [T] is
    monomorphic. Notice how [About state] doesn't say that [state] is template
    universe polymorphic, while it does for [prod]. So now the issue from
    earlier comes up again. *)
Definition state_pure {S T: Type} (t: T): state S T := fun s => (s, t).
Definition lazy_pure_state {S T: Type} (t: T): lazyT (state S T) :=
  lazy_pure (state_pure (S := S) t).
Fail Definition state_lazy {S T: Type} (t: T): state S (lazyT T) :=
  state_pure (S := S) (lazy_pure t).

(** Tricks to bypass the limitations of template universe polymorphism generally
    consist in exposing the template-polymorphic inductive, [prod] in this case,
    in order to get a fresh universe from it. Two examples are:
    - Inlining: expanding the definition of [state] in the examples above
      exposes [prod] which generates fresh universe levels. This doesn't
      prevent Rocq from later matching/unifiying the expanded term with the
      original [state], so it usually works as long as you can dig deep enough
      to find the problematic inductive. Of course, this comes at the cost of
      breaking any nice abstractions you might have.
    - Eta-expansion: writing [prod] without arguments doesn't generate fresh
      universes for the purpose of template polymorphism, so eta-expanding to
      [fun A B => prod A B] can help relax universe constraints. *)

(** These limitations are rather annoying because constructions based on [prod]
    are _everywhere_ in the standard library and in projects. The state monad is
    just one in a million. It's also the same problem with [sum] and many other
    core types like [list]. *)
About sum.
About list.

(** ** 4. A taste of “full” universe polymorphism ***)

(** *** Principle *)

(** Template universe polymorphism is limited in that it only applies to
    inductives and any indirect uses of such a type are just monomorphic. The
    proper way to have universe polymorphism is to allow it on any definition so
    that quantification can remain when defining things like state.

    Universe polymorphism extends the language of universes with universe
    parameters, which are similar to universe variables except that they are
    quantified over by definitions. *)

(** We can enable universe polymorphism from here onward with [Set Universe
    Polymorphism]. We need it on basically every type and definition. *)
Set Universe Polymorphism.
Inductive pprod (A B: Type) := ppair (a: A) (b: B).
About pprod.

(** Notice how [pprod] has _universe parameters_ [u] and [u0]. We can
    instantiate [pprod] with different such parameters and this will yield
    many variations of the same definition in as many universes. *)
Check pprod@{Set Set}.
Check pprod@{uprod uprod}.

(** So far, this is the same as template universe polymorphism. *)

(** *** Universe polymorphic definitions *)

(** The new trick is that definitions derived from [pprod] can retain the
    polymorphism by having their own universe parameters. *)
Definition pstate (S: Type) := fun (T: Type) => S -> (pprod S T).
About pstate.

(** Now [pstate] also has universe parameters and the expressiveness of [pprod]
    is no longer lost. *)
Definition pstate_pure {S T: Type} (t: T): pstate S T := fun s => ppair _ _ s t.
Definition lazy_pure_pstate {S T: Type} (t: T): lazyT (pstate S T) :=
  lazy_pure (pstate_pure (S := S) t).
Definition pstate_lazy {S T: Type} (t: T): pstate S (lazyT T) :=
  pstate_pure (S := S) (lazy_pure t).

(** This solution completely solves the state issue from our running example...
    with the drawback of redefining the product type, which creates friction
    with the standard library. *)
