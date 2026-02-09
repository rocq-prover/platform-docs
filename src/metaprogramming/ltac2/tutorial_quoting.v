(** * Tutorial Ltac2: Quoting

    *** Main contributors

    - Gaëtan Gilbert

    *** Summary

    Quoting provides syntax to embed one language in another. In
    particular, Ltac2 provides syntax to embed and to be embedded in
    Gallina (the language of terms) and Ltac1.

    *** Table of content

      - 1. Names (ident / @, reference)
      - 2. Terms and Ltac2
        - 2.1 Terms in Ltac2
        - 2.2 Ltac2 in terms
        - 2.3 Performance note
        - 2.4 Preterm and Ltac2 in term notations
      - 3. Quotations as Ltac2 notations
      - 4. Ltac1 and Ltac2

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

(** ** 1 Names (ident / @, reference)

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

(** ** 2 Terms and Ltac2

    *** 2.1 Terms in Ltac2

    The language of Rocq terms (Gallina) and the Ltac2 language do not
    have the same grammar.

    For instance, [forall n, n + 0 = n] is a Gallina expression which
    does not parse as a Ltac2 expression, and [fun () => 0] is a Ltac2
    expression which does not parse as a Gallina expression.

    However we can write a Ltac2 expression which contains a Gallina expression:
*)

Ltac2 Eval constr:(forall n, n + 0 = n).

(** The Ltac2 expression [constr:(...)] has type [Ltac2.Init.constr]
    (short name [constr]).

    It is considered ill-formed if the term mentions unknown variables:
*)
Fail Ltac2 Eval constr:(x).

(** To be precise, the term is internalized (see "internalization"
    through the glossary index in the reference manual) when the ltac2
    expression is typechecked.

    When the ltac2 expression is evaluated, it typechecks (see "type
    inference" through the glossary index in the reference manual) the
    given term, returning the elaborated term.

    Because typechecking a term requires a context (which contains the
    hypotheses), it throws an error if more than one goal is focused.
    If no goal is focused (such as in the previous "Ltac2 Eval", the
    section context (empty when there are no sections) is used instead
    of the goal context. *)
Goal True /\ True.
  Fail split; let _ := constr:(0) in ().
  (** The error is "thrown", meaning it cannot be caught by "try" and
      can only be caught at toplevel with "Fail". *)
  Fail try (split; let _ := constr:(0) in ()).
Abort.

(** [constr:(...)] runs typeclass inference at the end of
    typechecking, and fails if typechecking produced an new
    existential variables: *)
Fail Ltac2 Eval constr:(_).

(** When we want to allow new existential variables, we use
    [open_constr:(...)] instead of [constr:(...)]. Note that
    open_constr does not run typeclass inference.

    [open_constr:(...)] has type [constr], and the [Ltac2 Eval]
    printer prints the result of evaluating it using [constr:(...)].

    The only difference between the [open_constr:(...)] and
    [constr:(...)] syntaxes are in how they are evaluated.

    Try not to confuse [constr] as a Ltac2 type and the quotation
    syntax [constr:(...)]. *)
Ltac2 Eval open_constr:(_).

(** [open_constr:(...)] is more common than [constr:(...)] in
    practice, so it has a shorter syntax ['term] (a quote character
    followed by a term, at low parsing level when parentheses are not used). *)
Ltac2 Eval 'nat.
Ltac2 Eval '(0 + _).

(** *** 2.2 Ltac2 in terms

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

(** *** 2.3 Performance note

    We have seen that [open_constr:(...)] and [constr:(...)] differ in
    whether new evars are allowed, and mentioned that [constr:(...)]
    runs typeclass inference.

    There is another difference: [constr:(...)] substitutes all
    defined evars by their bodies in the returned term. Because
    defined evars are indistinguishable from their bodies, this
    difference only matters for performance. The main impact is that
    it makes recursive term construction using [constr:(...)]
    quadratic as the progressively constructed terms are repeatedly
    traversed to do the evar expansions: *)

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

(** *** 2.4 Preterms and Ltac2 in term notations

    A value of type [Ltac2.Init.preterm] (short name [preterm])
    corresponds to a term which has been internalized (see
    "internalization" through the glossary index in the reference
    manual) but not typechecker (see "type inference" through the
    glossary index in the reference manual).

    We may produce such values using the [preterm] quotation, for
    instance if we don't want typechecking: *)
Ltac2 Eval preterm:(fun x : 0 => x).

(** A preterm may be turned into a value of type [constr] (not to be
    confused with the [constr:(...)] quotation) by using
    [Ltac2.Constr.pretype], which runs typechecking like the
    [constr:(...)] quotation, or [Ltac2.Constr.Pretype.pretype] if we
    want more control (for instance to skip typeclass inference). *)
Fail Ltac2 Eval Constr.pretype preterm:(fun x : 0 => x).
Ltac2 Eval Constr.pretype preterm:(fun x => x + 0).

(** A Ltac2 variable [x] of type preterm may be quoted into terms
    using [$preterm:x].

    Typechecking [$preterm:x] will typecheck the preterm bound to [x]
    using the current flags of the surrounding term expression, and
    the expected type according to the typechecking algorithm.

    Multiple occurences of [$preterm:x] are typechecked independently.
    For instance in the following example the hole for the type of [x]
    produces separate existential variables, which are then
    instantiated by unification to [nat] and [bool].
 *)
Ltac2 Eval let id := preterm:(fun x : _ => x) in '($preterm:id 0, $preterm:id false).

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

(** ** 3 Quotations as Ltac2 notations

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

(** ** 4 Ltac1 and Ltac2

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
