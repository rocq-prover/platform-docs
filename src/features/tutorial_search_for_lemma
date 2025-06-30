(** * Search tutorial for Coq

    *** Summary

	This tutorial is about the powerful [Search] vernacular command in Coq.
	The [Search] command prints names and types of constants in the local or
	global context satisfying a number of criteria.

    *** Table of content

    - 1. Searching for lemmas
      - 1.1 Basic [Search] by name and type
        - 1.1.1 Exercise: find parity results on [nat]
      - 1.2 Search and notations
        - 1.2.1 Exercise: sum and products on [nat] and [Type]
      - 1.3 Searching using metavariables
        - 1.3.1 Exercise: find lemmas with metavariables
      - 1.4 Filtering on hypotheses (parameters) or conclusions (return type)
        - 1.4.1 Exercise: finding divisibility results
    - 2. Advanced [Search] options
      - 2.1 Disambiguating strings in Search queries
      - 2.2 Filtering results by logical kind and disjunctions of criteria.
      - 2.3 Searching inside or outside a specific module

    *** Prerequisites

    Needed:
    - For the first part, it suffices to have some basic experience of Coq: the
      user should know intuitively what is a Coq function and a Coq lemma or
      theorem. Scope notations are mentioned briefly but this should not be too
      much of an issue.
    - For the 2.3 part, some basic experience of Coq modules should be enough.

    Installation:
    This [Search] tutorial should work for Coq V8.16 or later.

    *** Warning

    When viewed in a web browser with jsCoq, some [Search] queries are slow
    (about 10 seconds).
*)

(** In this tutorial, we are going to search for lemmas, mostly about natural
    numbers.

    We already have all lemmas and definitions from the prelude ([Coq.Init]),
    and we require the library file [Coq.Arith.PeanoNat] which adds hundreds
    of new constants. *)

From Coq Require Import PeanoNat.

(** ** 1. Searching for lemmas *)

(** *** 1.1 Basic [Search] by name and type *)

(** In its most basic form, one searches for lemmas or definitions containing
   - a given constant, eg [Nat.add], or [nat]
   - a given string to be part of the identifier (the name)
*)

(** Search all lemmas or operations where the type [nat] occurs: *)
Search nat.

(** Search all lemmas or operations where [Nat.add] occurs: *)
Search Nat.add.

(** Search all lemmas or operations whose name contains "add": *)
Search "add".

(** In practice, we often want to search for lemmas satisfying multiple
    criteria, e.g. search for all lemmas whose name contain "add" _and_ whose
    type contains [Nat.mul].

    To do so, it suffices to give these criteria to [Search], it acts as a
    conjunction: *)
Search "add" Nat.mul.

(** We can give as many criteria as we want. Below we search for constants
    which satisfy:
    - has "mul" in the name and
    - has [Nat.add] in the type and
    - has [Nat.odd] in the type *)
Search Nat.add "mul" Nat.odd.

(** We can also _filter out_ results satisfying a criterion with by prepending
    it with a minus [-] symbol.
    Say we're looking for a lemma stating that the sum of an even number and an
    odd number is odd: *)
Search Nat.odd Nat.add.

(** This is already good, but we're not interested in lemmas whose name
    contain "mul", so we can filter them out to get clearer results by adding
    [-"mul"]: *)
Search Nat.odd Nat.add -"mul".

(** **** 1.1.1 Exercise: find parity results on [nat] *)

(** We're interested in lemmas about parity in [nat].
    There are two complementary definitions of being even and being odd:
    - [Nat.Odd] and [Nat.Even] (in [Prop]) are the usual existentially
      quantified definitions;
    - [Nat.odd] and [Nat.even] (in [bool]) are functions which compute. *)
Print Nat.Odd.
Print Nat.Even.
Print Nat.odd.
Print Nat.even.
Compute Nat.even 42.
Compute Nat.odd 42.

(** Find all lemmas, with a precise enough search, which
    1. state an equivalence between being [Even] and being [even];
    2. state that the successor (function [S]) of an [even] number is [odd];
    3. state that the product of an [Even] number by any other number is [Even];
    4. state that a number is [Even] or (predicate [or]) [Odd] and
    5. state that it is [true] that a number is [even] or (boolean operation
       [orb]) [odd].
*)

(* Beginning of solution *)
(* 1. *) Search Nat.Even Nat.even -Nat.add.
(* 2. *) Search Nat.even Nat.odd S.
(* 3. *) Search Nat.mul Nat.Even -Nat.add -Nat.Odd.
(* 4. *) Search or Nat.Even Nat.Odd -Nat.add -Nat.mul.
(* 5. *) Search orb Nat.even Nat.odd -Nat.add -Nat.mul.
(* End of solution *)

(** *** 1.2 Search and notations *)

(** Previously, we have been using the names of the operations to [Search] for.
    It may be confusing that such names do not even appear in the output. *)
Search Nat.add Nat.mul Nat.div.

(** Indeed, Coq uses notations to display such results, and these are exactly
    what the user may expect. In fact, we often forget the names of operations
    such as [Nat.add].

    We can search using notations in the following way: *)
Search (_ + _) (_ * _) (_ / _).

(** Notice the wildcards [_] around the operators. We call [(_ * _)], [(_ + _)]
    and [(_ / _)] _[Search] patterns_.
    We will soon see how to write more sophisticated such patterns. *)

(** Alternatively, we can use strings (more about this later): *)
Search "+" "*" "/".

(** If we're interested in the name of the function or predicate associated to
    a given notation, we can use the [Locate] command which shows how Coq
    currently interprets a given notation: *)
Locate "_ + _".

(** That's unexpected, we actually have 2 different meanings for ["+"]!

    As a side note, the ["+"] operator between types is the disjoint union. It's
    fine if you don't know what this means, our only concern here is that it
    exists.

    Now, how does Coq choose between them? What is the current interpretation
    of ["+"]?. *)

Check 2 + 3. (* this looks ok with natural numbers *)
Fail Check nat + bool. (* this fails with types *)

(** Actually, we could have guessed it with the output of [Locate]: the default
    interpretation for "+", without curly braces on the sides is
    [Init.Nat.add].

    Another way to get this information is to use the [About] command: *)
About "_ + _".

(** We have seen that Coq allows to use the same notation in different context.
    In fact, there are many other uses of "+" in the standard library, it could
    be the addition between rational numbers, real numbers, ...

    The interpretation context for a notation is called a _notation scope_.
    When a notation is ambiguous, because it belongs to more than one scope,
    its default interpretation is the one in the last opened scope.

    We can display open scopes with the [Print Visibility] command, note that
    the more recently opened scopes (which have a higher priority) appear last.
*)
Print Visibility.

(** Here, the last scope is [nat_scope], we see all the notations associated
    to it: order relations ([<=], [<], ...) and operations ([+], [*], ...).

    If we want to use [+] with its interpretation in [type_scope], without
    changing the opened scope order, we can do so with a scope delimiting key:
*)
Check (nat + bool)%type.
About "_ + _".

(** Scope delimiting keys are abbreviations of scope names, usually obtained by
    removing the [_scope] suffix.

    One can see the delimiting key associated to a scope name with the
    [Print Scope] command. *)
Print Scope nat_scope.
Check (2 + 3)%nat. (* works regardless of the scopes order *)
Print Scope type_scope.

(** We can (and should) use delimiting keys in [Search queries] with patterns
    and notation strings:

    For instance, if we want to know lemmas about product types, we can write a
    [type] key: *)
Search (_ * _)%type.
Search "*"%type.

(** The following query do not depend on the scopes order: *)
Search (_ + _)%nat.
Search "+"%nat (_ * _)%nat "/"%nat.

(** We have used [Search] patterns with binary operators, similarly, we can
    search about a unary prefix operator, such as [~] (the negation), with: *)
Search (~ _).

(** In that case it was not necessary to write explicitly the [type] key, since
    the [~] notation does not belong to scope [nat_scope].
    In fact, the [~] currently has only one interpretation. *)
Locate "~ _".

(** Now, let's search for lemmas about distributivity of multiplication over
    addition on [nat].
    To do so, we can first search all lemmas where the type [nat] and the
    operators (_ * _) and (_ + _) occur. *)
Search nat (_ + _) (_ * _). (* still too much *)

(** Since our current scope is [nat], the first search item is useless.
    We can ask for distributivity lemmas, these contain the string "distr" in
    their names. *)
Search (_ + _) (_ * _) "distr".

(** **** 1.2.1 Exercise: sum and products on [nat] and [Type] *)

(** Write [Search] commands with notations to find out if:
    1. there are operations whose return type is a product type containing [nat];
    2. there are lemmas involving [nat] and a sum type;
    3. there are inequalities (predicate [<=]) on [nat] stating that a sum is
       less than or equal to a product. *)

(* Beginning of solution *)
(* 1. *) Search (_ * _)%type nat.
(* 2. *) Search nat (_ + _)%type.
(* 3. *) Search (_ + _ <= _ * _)%nat.
(* End of solution *)

(** *** 1.3 Searching using metavariables *)

(** We have cheated a little bit. It often happens that we have no idea how
    a lemma is named. However, we know what distributivity (say, on the left)
    is. We can use a more precise pattern instead of (_ * _). *)
Search (_ * (_ + _) = _). (* nailed it *)

(** What about the commutativity of [Nat.add]? *)
Search (_ + _ = _ + _).

(** The list is somewhat manageable (and, by sheer luck, [Nat.add_comm] appears
    first), but we can be much more precise with meta-variables. *)
Search (?a + ?b = ?b + ?a).

(** We can even search for all commutativity lemmas: *)
Search (?op ?a ?b = ?op ?b ?a).

(** If we want to exclude the [bool] commutativity lemmas, we can, as before
    add the restriction that we want [nat] to be involved: *)
Search nat (?op ?a ?b = ?op ?b ?a).

(** Another possibility is to exclude any results mentioning [bool]: *)
Search (?op ?a ?b = ?op ?b ?a) -bool.

(** We can also opt to remove only results with "orb" it its name: *)
Search (?op ?a ?b = ?op ?b ?a) -"orb".

(** Or results where the (_ || _) operator appears (notice the scope key, since
    [bool_scope] is not currently opened): *)
Search (?op ?a ?b = ?op ?b ?a) -(_ || _)%bool.

(** **** 1.3.1 Exercise: find lemmas with metavariables *)

(** Write [Search] commands with notations and metavariables to find out:
    1. a lemma stating that adding a natural number on the right cannot be
       decreasing;
    2. left distributivity lemmas (without using "distr") between any two
       operations and
    3. a lemma saying that a divisor (relation [Nat.divide]) is less than or
       equal to the number it divides (does it have conditions?)
*)
(* Beginning of solution *)
(* 1. *) Search (?a <= ?a + _).
(* 2. *) Search (?op1 ?a (?op2 ?b ?c) = ?op2 (?op1 ?a ?b) (?op1 ?a ?c)).
(* 3. *) Search ((Nat.divide ?a ?b) -> ?a <= ?b).
(* End of solution *)

(** *** 1.4 Filtering on hypotheses (parameters) or conclusions (return type) *)

(** It often happens that we [Search] in the middle of a proof for a lemma we
    suspect will apply to the current goal. In that case, we can use
    the [concl:] specifier to restrict the [Search] output to results where
    a pattern (or notation) appears in the conclusion (a.k.a. return type). *)
Search concl:(_ + _ <= _).
Search concl:"||".

(** Of course, the [hyp:] specifier also exists to [Search] for a pattern or
    notation occurring in one of the hypotheses (a.k.a. parameters): *)
Search hyp:(_ + _ <= _).

(** We can be even more precise and specify that our pattern (or notation)
    should appear at the head of the conclusion (or an hypothesis), that is,
    the whole term should match our pattern, instead of a subterm.

    As an example, let us [Search] for lemmas about conjunctions and
    disjunctions.
    We want lemmas whose conclusion is a conjunction.
    We exclude [nat] in order to get only purely logical properties. *)
Search (_ \/ _) concl:(_ /\ _) -nat.

(** Notice that, in [Decidable.not_iff] and [bool_choice], the conclusion
    _contains_ a conjunction but is not a conjunction. We can exclude them
    with the [headconcl] specifier: *)
Search (_ \/ _) headconcl:(_ /\ _) -nat.

(** The equivalence [Decidable.not_or_iff] has also disappeared, because
    it is actually treated as a lemma having a single conclusion of the form
    [(_ <-> _)], hence not of the form [(_ /\ _)]. *)

(** We can list all lemmas about addition with an equivalence as a conclusion: *)
Search "+" headconcl:"<->".

(** and all lemmas having an equivalence as a hypothesis. *)
Search headhyp:"<->".

(** Finally the [head] keyword is just a shorthand for [headconcl] or
    [headhyp]: *)
Search head:"<->".

(** **** 1.4.1 Exercise: finding divisibility results *)

(** Write [Search] commands with filters on hypotheses and/or conclusions in
    order to:
    1. find (again) a lemma saying that divisors of an natural number are less
       than or equal to this number;
    2. what can be said when a natural number divides a product and
    3. all results whose goals are exactly divisibility statements.
*)
(* Beginning of solution *)
Search concl:(_ <= _) hyp:Nat.divide.
Search hyp:(Nat.divide _ (_ * _)).
Search headconcl:Nat.divide.
(* End of solution *)

(** ** 2. Advanced [Search] options *)

(** *** 2.1 Disambiguating strings in Search queries *)

(** We have seen two different usages of strings in search queries, namely,
    searching for constants whose name contains the string, such as: *)
Search "comm".

(** or, search for constants whose type contain a notation, such as: *)
Search "||".
Search "+".

(** So, what really happens here?
    First, Coq makes a different between identifier (name) characters and
    other characters.
    The characters '|' and '+' cannot be used in constant names, so Coq guesses
    it should interpret "||" and "+" as notations to appear in the types, not as
    substrings of names.

    What happens when a notation uses only identifier characters?
    This is the case for the [mod] operator: *)
About "mod".

(** Searching for "mod" lists constants whose identifiers contain "mod", as
    is indicated in the [divmod] operation here: *)
Search "mod".

(** To [Search] for constants where the notation [mod] appears in the type, we
    have two solutions: either we enclose the string with single quotes: *)
Search "'mod'".

(** or we give an explicit scope key (hence it must be a notation): *)
Search "mod"%nat.

(** Of course, we can still use a pattern instead of a string: *)
Search (_ mod _).

(** *** 2.2 Filtering results by logical kind and disjunctions of criteria. *)

(** We can also [Search] for a constant defined with a specific keyword.
    For instance, the following lists all [Lemma]s whose names contain "add"
    and types contain [0]: *)
Search "add" 0 is:Lemma.

(** Same for constants defined with the [Theorem] keyword: *)
Search "add" 0 is:Theorem.

(** Now, if we want both [Lemma]s and [Theorem]s we can use the general
    "or" construct in [Search] queries: *)
Search "add" 0 [is:Theorem | is:Lemma].

(** The following lists lemmas and theorems about [Nat.add] or [Nat.mul]
    containing the strings "comm" or "assoc": *)
Search [Nat.add | Nat.mul] ["comm" | "assoc"] [is:Lemma | is:Theorem].

(** The interested reader can refer to
    [the reference manual](https://coq.inria.fr/doc/V8.19.0/refman/proof-engine/vernacular-commands.html?highlight=search#search-by-keyword)
    for the list of all logical kinds which can appear after [is:]. *)

(** *** 2.3 Searching inside or outside a specific module *)

(** Finally it is possible to further restrict the [Search] results inside or
    outside a specific [Module]. *)
Search concl:"+" concl:"*" headconcl:(_ < _) inside Nat.

(** The [in] keyword is a shorthand for [inside]: *)
Search concl:"+" concl:"*" headconcl:(_ < _) in Nat.

(** The [outside] keyword on the contrary excludes results from a specific
    [Module]. *)
Search "+" outside Nat.

(** Now, these last [Search]es exhibit a subtlety related to the [Module]
    System. Actually, there are two modules named [Nat] in our environment. *)

(** The first to appear is the last to be [Require]d. In our case, its full
    name is [Coq.Arith.PeanoNat.Nat]: *)
About Nat.
Print Module Nat.

(** But this [Nat] module shadows the [Nat] module which already exists in
    [Init] (actually, as a side note, the [Coq.Init.Nat] module is [Include]d
    in [Coq.Arith.PeanoNat.Nat], but this is not relevant in this tutorial). *)

(** If one wants to [Search] for all lemmas in the [Nat] module taken from
    [Init], it suffices to qualify it more to disambiguate it: *)
Search _ in Init.Nat.

(** We can even shadow [PeanoNat.Nat] module in this file: *)
Module Nat.
  Lemma foo : 21 + 21 = 42.
  Proof. reflexivity. Qed.
End Nat.

Search _ in Nat.
Search "f" "o" in PeanoNat.Nat.

(** The take-home message here is that modules are often used to provide
    namespace facilities, so when using [inside] and [outside], one should
    often qualify them more. *)
