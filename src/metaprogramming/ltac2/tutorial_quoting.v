(** * Tutorial Ltac2: Quoting

    *** Main contributors

    - Gaëtan Gilbert

    *** Summary

    Quoting provides syntax to embed one language in another. In
    particular, Ltac2 provides syntax to embed and to be embedded in
    Gallina (the language of terms) and Ltac1.

    *** Table of content

      - 1. Names (ident / @, reference)
      - 2. Quoting: Using Rocq's Terms in Ltac2
        - 2.1 Quoting Terms
        - 2.2 Quoting Terms Without Existantial Variables
        - 2.3 Preterms : Internalize without Typechecking
      - 3. Ltac2 in terms
      - 4. Quotations as Ltac2 notations
      - 5. Ltac1 and Ltac2

    *** Prerequisites

    Needed:
    - Basic knowledge of Ltac2

    Installation:
    - Ltac2 and its core library are available by default with Rocq.
*)

(** Load Ltac2 *)
From Ltac2 Require Import Ltac2.

(** Enable "printf" Ltac2 notation *)
From Ltac2 Require Import Printf.

(** ** 1. Names (ident / @, reference)

    The grammar of names may be trivial but it still needs some syntax
    to produce name constants in Ltac2 expression.

    For identifiers, [ident:(x)] and [@x] are equivalent Ltac2 expressions
    which evaluate to the name "x" (of Ltac2 type [Ltac2.Init.ident], short name [ident]). *)
Ltac2 Eval (ident:(x), @y).

(** A slight printing inconsistency: the evaluated identifier is
    printed ith the [@] syntax, but the non evaluated Ltac2 expression
    is printed with [ident:(...)]: *)
Ltac2 make_x () := @x.
Print make_x.

(** Ltac2 also has syntax for term references (constants, inductive
    types, inductive constructors, section variables and hypotheses of
    the goal context). This corresponds to type [Ltac2.Std.reference]
    (short name [Std.reference] with our current Imports). *)
Ltac2 Eval reference:(nat).
(** Unfortunately automatic printing of such values is currently quite bad: [Std.IndRef <abstr>].
    The easiest way to print it is to use [Env.instantiate] to turn the reference into a term: *)
Ltac2 Eval Env.instantiate reference:(nat).

(** The name is resolved when the Ltac2 expression is typechecked, not when it is evaluated: *)
Fail Ltac2 Eval fun () => reference:(does_not_exist).

(** Using [&] forces the name to be interpreted as a variable name,
    without checking (we do not check because variables may be
    dynamically introduced, see [&] in section 2.2 of this tutorial):
 *)
Ltac2 Eval reference:(&does_not_exist).


(** ** 2. Quoting: Using Rocq's Terms in Ltac2

  The language of Rocq terms (Gallina) and the Ltac2 language are not the
  same language, and do not have the same grammar.

  For instance, [forall n, n + 0 = n] is a Gallina expression which
  does not parse as a Ltac2 expression, and [fun () => 0] is a Ltac2
  expression which does not parse as a Gallina expression.

  A Rocq term is not a Ltac2 expression, as is, but it can be turned into
  a Ltac2 expression we can manipulate, in different ways.
  Such an operation is call "quoting" (from Rocq to Ltac2).

  *** 2.1 Quoting Terms

  The most common method to quote a Rocq term, is to ['].
  Its resulting type will be [constr], the type of Rocq term in [Ltac2].
*)

Ltac2 Eval '(forall n, n + 0 = n).

(** A term [t] is quoted in two steps:

  1. The term is internalized when the Ltac2 expression is typechecked.
     This does several things like name resolution or interpreting notations.
     See "internalization" through the glossary index in the reference manual.

  2. When the Ltac2 expression is evaluated, the internalization of [t]
     is typechecked in the current context, returning the elaborated term.
     See "internalization" through the glossary index in the reference manual.

  Note that [open_constr:] does not run typeclass inference.

  For instance, trying to quote an undefinied variable returns an error:
*)

Fail Ltac2 Eval '(x).

(** Moreover, because typechecking a term requires a context (which contains the
    hypotheses), it throws an error if more than one goal is focused.
    For instance, the following fails as there are two goals after [split]:
*)

Goal True /\ True.
  Fail split; let _ := '(0) in ().
Abort.

(** Moreover, this error is "thrown", meaning it cannot be caught by "try" and
    can only be caught at toplevel with "Fail". *)
Goal True /\ True.
  Fail try (split; let _ := constr:(0) in ()).
Abort.

(** If no goal is focused the section context (empty when there are no sections)
    is used instead of the goal context.
*)

Section foo.
  Variable (A : nat).

  Ltac2 Eval 'A.

End foo.

(** ['] is an notation for [open_constr:]. The name [open_constr] comes
    from the fact that quoted terms can includ existantial variables.
    This is very practical to write tactics.

    For instance, suppose, we have an hypothesis [forall x : A, B x] we want to specialize.
    We would like to create a new goal of type [A], to prove [x : A] using tactics.

    We can do so by:
    1. Recovering the type [?a] by matching the type of the hypothesis
    2. Creating a new existantial variables with [(_ :> a)],
    3. Quoting it [let e := '(_ :> ?a)] to get a Ltac2 expression we can manipulate
    4. Specialize the hypothesis [h] with [specialize ($h $e)]
    5. Following these steps, the existential variables is shelved.
       Therefore, to create a goal [A], we wrap the expression in [unshelve].

    Combined, this gives us the following small tactic:
*)

Ltac2 forward (h : ident) :=
  let h := Control.hyp h in
  lazy_match! Constr.type h with
  | forall (_ : ?a), _ =>
      unshelve (
        let e := '(_ :> $a) in
        specialize ($h $e)
      )
  end.

(** To refer to an hypothesis [H], we use [@H]*)

Goal (forall n, n = 4) -> 5 = 4.
  intros H. forward @H.
  - exact 5.
  - assumption.
Qed.

(** We can also wrap it in a notation, to do the quoting for us *)

Ltac2 Notation "forward" h(ident) := forward h.

Goal (forall n, n = 4) -> 5 = 4.
  intros H. forward H.
  - exact 5.
  - assumption.
Qed.

(** *** 2.2 Quoting Terms Without Existantial Variables

  It also possible to quote terms without allowing existential variables, using
  the quotation [constr:] instead of [open_constr:].
  For instance, quoting a wildcard [_] fails for [constr:]:
*)

Fail Ltac2 Eval constr:(_).

(** As for [open_constr], the resulting type of [constr:] is the type [constr]
    Try not to confuse the Ltac2 type [constr], and the quotation syntax [constr:(...)].

    As you may have noticed, the error message above is referring to instances:
    "Could not find an instance for the following existential variables:?y : ?T".
    The reasons is that to solve existantial variables, opposite to [open_constr:],
    [constr:] runs typeclass inference.

    Another difference is that [constr:(...)] substitutes all defined evars by
    their bodies in the returned term. Because defined evars are
    indistinguishable from their bodies, this difference only matters for
    performance. The main impact is that it makes recursive term construction
    using [constr:(...)] quadratic as the progressively constructed terms are
    repeatedly traversed to do the evar expansions:
*)

Ltac2 rec nat_of_int (succ : constr -> constr) (n:int) :=
  if Int.equal n 0 then
    (* here constr vs open_constr does not matter since 0 is a trivial term *)
    constr:(0)
  else succ (nat_of_int succ (Int.sub n 1)).

(** If [succ] uses [open_constr:(...)], [nat_of_int] is linear in [n]: *)
Time Ltac2 Eval nat_of_int (fun x => '(S $x)) 5000.

(** but with [constr:(...)] it is quadratic (n = 5000 is enough to
    notice the slowdown without taking very long on the author's
    machine, use a higher number if you have a faster machine). *)
Time Ltac2 Eval nat_of_int (fun x => constr:(S $x)) 5000.

(** You can play with th value of [n] to see the performance curve,
    for instance 10_000 should take twice the time with
    [open_constr:(...)] but four times with [constr:(...)]. *)


(** *** 2.3 Preterms : Internalize without Typechecking

    In some case, we want to manipulate a Rocq term in Ltac2, but do not want
    to typecheck it as quoting does. Two main examples are:
    - we have more than one goal, and need to postpone typehecking to focus first
    - because we want to do typechecking differently, e.g. with coercions disable

    In other words, we want to internalize a term, but postpone typechecking,
    and trigger it by hand. This is possible, and corresponds to the Ltac2 type
    [preterm], which can be created using the quotation [preterm:]. For
    instance, let us quote a term that does not typecheck.
*)

Ltac2 Eval preterm:(fun x : 0 => x).

(** A preterm can then be turned into a value of type [constr] using
      [Ltac2.Constr.pretype], which runs typechecking.
      (or [Ltac2.Constr.Pretype.pretype] for more control *)
Fail Ltac2 Eval Constr.pretype preterm:(fun x : 0 => x).
Ltac2 Eval Constr.pretype preterm:(fun x => x + 0).

(** As an example, consider writing a small function [exists].
    If we write a notation for it naively, then it will fail when linked with
    [;] with another tactic, because there will be two goals:
*)

Ltac2 exists0 (t : constr) :=
  unshelve (econstructor 1) > [exact $t |].

Ltac2 Notation "exists" t(constr) := exists0 t.

Goal {n | n <= 0} * {n | n <= 0}.
  Fail split; exists 0.
Abort.

(** We need to postpone typechecking to after focusing the goals.
    We can do so by quoting a [preterm] rather than a [constr], then typechecking by hand.
*)

Ltac2 Notation "exists" t(preterm) :=
  Control.enter (fun () => exists0 (Constr.pretype t)).

(** It now works as expected *)

Goal {n | n <= 0} * {n | n <= 0}.
  split; exists 0.
Abort.

(** A Ltac2 variable [x] of type preterm may be unquoted into Rocq terms using [$preterm:x].

    Typechecking [$preterm:x] will typecheck the preterm bound to [x]
    using the current flags of the surrounding term expression, and
    the expected type according to the typechecking algorithm.

    Multiple occurences of [$preterm:x] are typechecked independently.
    For instance in the following example the hole for the type of [x]
    produces separate existential variables, which are then
    instantiated by unification to [nat] and [bool].
 *)
Ltac2 Eval
  let id := preterm:(fun x : _ => x) in
  '($preterm:id 0, $preterm:id false).

(** Preterms also occur naturally when quoting Ltac2 inside a notation definition:
    the notation variables are bound as Ltac2 variables of type preterm in the Ltac2 expression.

    Inside the Ltac2 expression they are not bound as term variables:
 *)
Fail Notation "x ++ y" := (x + ltac2:(exact y)).

(** and not bound with type constr: *)
Fail Notation "x ++ y" := (x + ltac2:(exact $y)).

(** but they are bound with type preterm: *)
Notation "x ++ y" := (x + ltac2:(exact $preterm:y)) (only parsing).

Check _ ++ 1.

(** Since we used [exact] in the notation, it rejects unsolved existential variables on the right: *)
Fail Check 0 ++ _.

(** Note that preterms close over (contain a copy of) the Ltac2 bound
    variables visible when it is created. For instance the following
    produces "0" not "1": *)
Ltac2 Eval let x := '0 in let y := preterm:($x) in let x := 1 in Constr.pretype y.

(** and the following does not produce a "unbound variable x" error: *)
Ltac2 Eval let y := let x := '0 in preterm:($x) in Constr.pretype y.

(** and in general functions like the following work as expected: *)
Ltac2 succ_preterm (x:preterm) := preterm:(S $preterm:x).

Ltac2 Eval Constr.pretype (succ_preterm (succ_preterm (succ_preterm preterm:(0)))).


(** *** 3. Ltac2 in terms

    We can write a Ltac2 expression inside a Gallina expression: *)
Check ltac2:(exact 0).

(** The ltac2 expression is typechecked when the Gallina term is
   internalized (see "internalization" through the glossary index in
   the reference manual). It should have type [unit], but other types
   are tolerated (with a warning).

   When the Gallina term is typechecked (see "type inference" through
   the glossary index in the reference manual), a new existential
   variable is created whose context is the context of the quotation
   (i.e. the context of the full Gallina expression extended with any
   local variables) and conclusion if the expected type of the
   quotation according to the typechecking algorithm.

   The Ltac2 tactic is then evaluated with that evar as the single
   focused goal.

   If there is no expected type (for instance in the above Check), a
   fresh type evar is also created in the same context to be the
   conlusion.

   The term produced by the quotation is the evar, which is typically
   instantiated by the tactic (for instance by [0] in the above Check).

   If the tactic fails, it causes typechecking the term to fail:
 *)
Fail Check ltac2:(Control.zero Not_found).

(** Ltac2 internalizes terms without awareness of what variables may
    have been introduced by a previous tactic. For instance: *)
Fail Ltac2 intro_then_exact () := intros x; exact x.

(** When we need to refer to such a dynamically introduced variable,
    we can use the [&x] syntax: *)
Ltac2 intro_then_exact () := intros x; exact &x.

(** [&x] actually expands to [ltac2:(Control.refine (fun () => Control.hyp @x))].
    We can see it if we print the above definition: *)
Print intro_then_exact.

(** Because goal contexts cannot contain duplicated names, the names
    of local variables may be mangled when generating the existential
    variable to run the quoted tactic: *)
Check fun (x:nat) (x:bool) => (&x, &x0).
(** The result prints [fun x x0 => (x0, x)]: in general name mangling
    when generating the evar context does not match name mangling done
    by printing, and it should not be relied upon. *)


(** When we quote a term inside a Ltac2 expression, it is common to
    want to refer back to a Ltac2 variable which is bound to a term.
    We can use the general quotation for this:
 *)
Ltac2 Eval let x := '1 in '(ltac2:(refine x) + ltac2:(refine x)).

(** but for more convenience we also have the [$x] syntax: *)
Ltac2 Eval let x := '1 in '($x + $x).

(** Note that [$x] is generally equivalent to [ltac2:(refine x)] but
    does not actually expand to it and may have differences. In
    particular, [$x] does not need to generate an existential variable
    to run a tactic, it directly expands to the term bound to Ltac2
    variable [x]. *)


(** ** 4. Quotations as Ltac2 notations

    Most (all?) Ltac2 quotations do not need to be primitive (though
    they often are) and can be written as Ltac2 notations.

    (Note: this is only the case for quotations embedding some syntax
    in Ltac2 syntax, not in the other direction. For instance
    [ltac2:(...)] in terms currently must be primitive syntax.)

    For instance we can define a notation equivalent to [ident:(...)]:
*)
Ltac2 Notation "myident" ":" "(" x(ident) ")" := x.
Ltac2 Eval myident:(x).

(** or a notation equivalent to [']: *)
Ltac2 Notation "#" x(open_constr) := x.
Ltac2 Eval #(0 + _).

(** In fact even the [constr] and [open_constr] notation arguments
    ("syntactic classes") do not need to be primitive and could be
    implemented on top of [preterm]. For instance the following
    notation provides a short quotation equivalent to [constr:(...)]: *)
Ltac2 Notation "##" x(preterm) := Constr.pretype x.

(** Exercise: define a [open_constr_with_tc:(...)] quotation
    equivalent to [open_constr:(...)] but without skipping typeclass
    inference.

    Hint: [Ltac2.Constr.Pretype.open_constr_flags_no_tc] makes
    [Ltac2.Constr.Pretype.pretype] behave like [open_constr:(...)]. *)

(** Exercise: define a [fast_constr:(...)] quotation equivalent to
    [constr:(...)] but without substituting defined evars, such that
    using it with [nat_of_int] is fast.

    Hint: [Ltac2.Constr.Pretype.Flags.set_nf_evars] is used to control
    the evar substitution.
 *)
(* Ltac2 Notation "fast_constr" ... *)
(* Ltac2 fast_constr_succ (x:constr) : constr := fast_constr:(S $x). *)
(* Time Ltac2 Eval nat_of_int fast_constr_succ 5000. *)


(** ** 5. Ltac1 and Ltac2

    We can embed a Ltac1 expression into Ltac2 using [ltac1:(...)].
    The resulting Ltac2 expression has type [unit], and evaluating it
    runs the Ltac1 tactic: *)
Ltac2 Eval ltac1:(idtac "hello from Ltac1").

(** Ltac1 tactics quoted into Ltac2 can be quantified over Ltac1
    variables using [ltac1:(x1 .. xn |- ...)]. This produces a ltac2
    expression of type [Ltac1.t -> .. -> unit], with [n] [Ltac1.t]
    arguments. *)
Ltac2 Eval ltac1:(x y |- idtac x).

(** Values of type [Ltac1.t] may be constructed using the APIs in module [Ltac2.Ltac1]. *)
Ltac2 Eval ltac1:(x y |- idtac y) (Ltac1.of_constr '42) (Ltac1.of_ident @xx).

(** (note that in Ltac1 printing terms automatically focuses on each
    current goal, so it produces no output when there are no goals:) *)
Ltac2 Eval ltac1:(x y |- idtac x y) (Ltac1.of_constr '42) (Ltac1.of_ident @xx).

(** We can also produce values of type [Ltac1.t] by quoting Ltac1
    expressions with [ltac1val:(...)] (which supports the same
    [ltac1val:(v1 .. vn |- ...)] syntax to quantify over variables): *)
Ltac2 Eval ltac1val:(let x := constr:(42) in x).

(** Such values can be cast to Ltac2 types using the APIs in module
    [Ltac2.Ltac1]. Since Ltac1 is dynamically typed such casts can
    fail (returning None).

    Ltac1 semantics of returning values are way beyond the scope of
    this tutorial, and for instance the following ltac1val is NOT a
    constr and the cast returns [None]: *)
Ltac2 Eval Ltac1.to_constr ltac1val:(let x := constr:(42) in x).

(** We can also embed Ltac2 inside Ltac1 using [ltac2:(...)] which
    runs the Ltac2 tactic when evaluated: *)
Ltac2 Eval ltac1:(ltac2:(printf "hello from Ltac2 inside Ltac1")).

(** The Ltac2 expression should have type [unit], but other types are
    tolerated with a warning (the returned value is ignored): *)
Ltac2 Eval ltac1:(ltac2:(0)).

(** The ltac2 expression may also quantify over variables with the
    "|-" syntax, and such variables will be bound with type [Ltac1.t].

    Ltac1 syntax does not support directly applying quotations ([ltac2:(x |- ...) vx])
    so we have to let-bind it:
 *)
Check
  (* [ltac:(...)] is not a Ltac2 quotation, but it is a quotation of
     Ltac1 into terms similar to [ltac2:(...)]. *)
  ltac:(
  let f :=
    ltac2:(x |-
      match Ltac1.to_constr x with
      | None => Control.throw Assertion_failure
      | Some x => exact $x
      end)
   in
   f 0).
