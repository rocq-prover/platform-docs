(** * Simple inductive types and the match construct *)

(** ** Enumerated types *)

(** In Rocq, the [Inductive] keyword is the main way to introduce new types. *)

(** Let us start with a very simple [clock] type: *)

Inductive clock :=
| tic
| tac.

(** Rocq informs us that [clock] is defined. Additionally, other constants
   ([clock_rect], ...) are defined, but let us ignore them for the moment. *)

(** [tic] and [tac] are both constants of type [clock]: *)

Check tic.
Check tac.

(** There is more: [tic] and [tac] are the sole _constructors_ of the type
    [clock]. Without going into details, this means that:
    - any value of type clock has to be either [tic] or [tac] ("no junk")
    - [tic] and [tac] are distinct values ("no confusion") *)

(** Let us prove first that [tic] and [tac] are distinct: *)
Lemma tic_not_tac : tic <> tac.
Proof.
  (* Assume that tic = tac *)
  intros H.
  (* Now, by construction, the assumption is a contradiction. *)
  (* Using [discriminate H] finishes the proof. *)
  discriminate H.
Qed.

(** In fact, [discriminate] on an equality between distinct constructors
    finishes _any_ proof. *)
Lemma tic_eq_tac_22 : tic = tac -> 2 + 2 = 5.
Proof.
  intros H. discriminate H.
Qed.

(** Now, the [destruct] tactic allows us to reason by cases on an inductive type
    with different constructors. *)
Lemma tic_or_tac (t : clock) : t = tic \/ t = tac.
Proof.
  (* We reason by cases on the possible values of [t] *)
  destruct t eqn:teq.
  - (* first case, [t = tic]; notice that t has disappeared in the goal, it
       would have disappeared completely if we had omitted [eqn:teq] *)
    left. reflexivity.
  - (* second case, [t = tac] *)
    right. reflexivity.
Qed.

(** For the moment, we hide what is behind [discriminate] and [destruct]. It
    is sufficient to have the "no junk" and "no confusion" principles in mind.
*)

(** To define functions on the [clock] type, we may use the [match] construct.
*)

Definition clock_to_0_1 (t : clock) :=
  match t with
  | tic => 0
  | tac => 1
  end.

(** The [clock_to_0_1] function takes a term of type [clock] as argument
   and returns a [nat]. *)
Check clock_to_0_1.

(** [Rocq] will perform reductions with [match], choosing the right case *)
Compute (clock_to_0_1 tac).
Compute (clock_to_0_1 tic).

(** We can also define a function of type [clock -> clock]. *)
Definition next (t : clock) :=
  match t with
  | tic => tac
  | tac => tic
  end.

Check next.
Compute (next (next (next tic))).

Lemma next_involutive (t : clock) : next (next t) = t.
Proof.
  destruct t eqn:t_eq.
  - (* first case: t = tic *)
    (* We compute with [next]: next (next tic) = next tac = tac *)
    simpl.
    reflexivity.
  - simpl. reflexivity.
Qed.

(** In fact, Rocq already performs all the possible reduction steps before
    checking for equality, so a shorter proof would be: *)
Goal forall (t : clock), next (next t) = t.
Proof. destruct t; reflexivity. Qed.

(** Exercise: define the following function from [clock] to [nat]:
    the image of [tic] should be [0] and the image of [tac] should be [1]. *)
Definition clock_to_nat (t : clock) := 42. (* to be replaced *)

(** Exercise: now prove that: *)
Lemma clock_to_nat_range (t : clock) :
  clock_to_nat t = 0 \/ clock_to_nat t = 1.
Proof.
Admitted. (* to be replaced with [Qed.] *)

(** Exercise: prove the following lemma *)
Lemma clock_not_tic (t : clock) : t <> tic -> t = tac.
Proof.
Admitted. (* to be replaced with [Qed.] *)

(** Let's move on to a more interesting enumerated type, the months: *)
Inductive month :=
| january
| february
| march
| april
| may
| june
| july
| august
| september
| october
| november
| december.

(** We want to define a function returning the number of days in a month,
    ignoring leap years. This is a good opportunity to show some syntactic sugar
    around the [match] construct. *)
Definition number_of_days (m : month) :=
  match m with
  | february => 28
  | april | june | september | november => 30
  | _ => 31
  end.

(** Notice how we could regroup cases and the catch-all case [_] in the end. *)
Check number_of_days.
Compute (number_of_days february).
Compute (number_of_days january).

(** We can easily prove that (in our simplified setting) the number of days
    is either 28 or 30 or 31. *)
Lemma range_number_of_days (m : month) :
  let n := number_of_days m in n = 28 \/ n = 30 \/ n = 31.
Proof.
  destruct m; simpl.
  (* We use goal selectors to make the proof shorter: *)
  2: left; reflexivity.
  (* the 2nd goal has disappeared, so [april], [june], etc have been shifted. *)
  3, 5, 8, 10: right; left; reflexivity.
  all: right; right; reflexivity.
Qed.

(** Exercise: define a season type *)
Inductive season := replace_me. (* to be replaced *)

(** Exercise: state and prove a lemma showing that your four seasons are the
    only possible values for the [season] type. *)

(** Exercise: define the [month_to_season] function, associating each month to a
    season. To simplify, use the season for which the month has a majority of
    days for this season, for instance the season associated to march is winter.
*)
Definition month_to_season (m : month) := 0. (* replace 0 with the definition *)

(** Exercise: inversion of month_to_season.
    State and prove a lemma showing that the only months whose season is
    spring are April, May and June. *)

(** *** Booleans *)

(** Booleans are certainly important enough to have a dedicated tutorial, but
    in case you have not encountered them, here they are, in all their glory: *)

Print bool.

(** They are not very different from our [clock] values.
    Note that they are not the same at all as the [True] and [False]
    propositions in [Prop]. *)

(** Boolean functions are defined with the [match] construct. *)

(** Here is the negation function: *)
Definition negb b := match b with true => false | false => true end.

(** Notice, in passing, that the first case in a [match] needs not be preceded
    with a vertical bar ([|]), the same holds for [Inductive] types, as you
    may have noticed in the output of [Print bool]. It is only a matter of style
    to write this first vertical bar or not.  *)

Check negb.
Compute (negb true).

(** The conjunction is defined by case analysis on the left operand: *)
Definition andb b1 b2 :=
  match b1 with
  | true => b2
  | false => b1
  end.

Infix "&&" := andb.

(** We can prove by case analysis: *)
Lemma andb_false_r b : b && false = false.
Proof.
  destruct b eqn:eq_b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(** Exercise: define [orb], the disjunction operator on booleans. *)
Definition orb (b1 b2 : bool) := false. (* replace false with your definition *)
Infix "||" := orb.

(** Exercise: prove the following lemmas: you may need (or not!) case
    analysis. *)
Lemma orb_true_l b : true || b = true.
Proof.
Admitted. (* to be replaced with [Qed.] *)

Lemma orb_true_r b : b || true = true.
Proof.
Admitted. (* to be replaced with [Qed.] *)

(** Exercise: prove the following lemmas: *)
Lemma true_neq_false : true <> false.
Proof.
Admitted. (* to be replaced with [Qed.] *)

(** Exercise: prove the following lemmas: *)
Lemma true_or_false b : b = true \/ b = false.
Proof.
Admitted. (* to be replaced with [Qed.] *)

(** Exercise: show that the following De Morgan's law holds : *)
Lemma negb_andb b1 b2 : negb (b1 && b2) = (negb b1) || (negb b2).
Admitted. (* to be replaced with [Qed.] *)

(** ** Constructors with arguments *)

(** The next step after enumerated types is to allow arguments in the
    constructors of a type.

    Let us consider a type which wraps natural numbers, boolean values or
    an error. *)

Inductive nat_bool_error :=
| some_nat (n : nat)
| some_bool (b : bool)
| an_error.

(** This type has 3 different constructors, the first two have arguments. *)
Check some_nat.
Check some_bool.
Check an_error.

(** Intuitively, an element of the type [nat_bool_error] is either a natural
    number, or a boolean, or an error (with no content). *)

(** Again, the "no junk" and "no confusion" principles hold, we can use
    the [discriminate] and the [destruct] tactics to reason about
    [nat_bool_error]: *)

Lemma some_nat_not_error (n : nat) : some_nat n <> an_error.
Proof. intros H. discriminate H. Qed.

(** There is more, constructors are one-to-one: *)

Lemma some_nat_0_not_1 : some_nat 0 <> some_nat 1.
Proof. intros H. discriminate H. Qed.

(** We can prove it in general, but to do so, it is less magical to write a
    (partial) inverse to the [some_nat] constructor. *)

Definition nat_bool_error_to_nat (x : nat_bool_error) :=
  match x with
  | some_nat n => n
  | some_bool b => if b then 1 else 0 (* somewhat arbitrary *)
  | an_error => 0 (* arbitrary value *)
  end.

(** Notice how we bound the arguments of the constructors in the patterns. *)

(** Again, the following rewrite rule is just Rocq reducing the left hand side.
 *)
Lemma nat_bool_error_to_nat_some_nat (n : nat) :
  nat_bool_error_to_nat (some_nat n) = n.
Proof. reflexivity. Qed.

(** With this partial inverse, we can prove that [some_nat] is one-to-one: *)
Lemma some_nat_injective (n m : nat) : some_nat n = some_nat m -> n = m.
Proof.
  intros H.
  rewrite <-(nat_bool_error_to_nat_some_nat n).
  rewrite <-(nat_bool_error_to_nat_some_nat m).
  rewrite H.
  reflexivity.
Qed.

(** Here is a more direct proof: we apply the function [nat_bool_error_to_nat]
    to the equality H directly.
    This can be done with the [f_equal] function whose type is: *)
About f_equal.

Goal forall (n m : nat), some_nat n = some_nat m -> n = m.
Proof.
  intros n m H.
  apply (f_equal nat_bool_error_to_nat) in H.
  exact H.
  (* Now, the interested reader may take a look at the proof term to see that
     indeed, the injectivity of the constructor [some_nat] is the ability
     to recover its argument with [match]. *)
  Show Proof.
Qed.

(** A partial inverse like [nat_bool_error_to_nat] can be very handy. But in
    many cases, we want to use the injectivity more quickly.
    Fortunately, the [injection] tactic does just that. *)

Goal forall (n m : nat), some_nat n = some_nat m -> n = m.
Proof.
  intros n m H.
  injection H as H.
  exact H.
  (* The interested reader may take a look at the proof term: it does use
     a similar partial inverse function. *)
  Show Proof.
Qed.

(** Notice the syntax of the [injection] tactic:
    [injection <name_of_hypothesis> as <name_of_new_hypothesis>]
    Since [injection] discards the hypothesis, we may as well use the same
    name (as we did in the previous example). *)

(** Exercise: using [injection], prove the following lemma. *)
Lemma some_bool_injective (b1 b2 : bool) :
  some_bool b1 = some_bool b2 -> b1 = b2.
Proof.
Admitted. (* to be replaced with [Qed.] *)

(** Exercise: do the same without [injection], with a partial inverse. *)
Definition nat_bool_error_to_bool (x : nat_bool_error) :=
  true. (* to be replaced *)
Goal forall (b1 b2 : bool), some_bool b1 = some_bool b2 -> b1 = b2.
Proof.
Admitted. (* to be replaced with [Qed.] *)

(** Now, let us move on to reasoning by case analysis on elements of type
    [nat_bool_error]. *)
Lemma nat_bool_error_cases (x : nat_bool_error) :
  (exists n, x = some_nat n) \/ (exists b, x = some_bool b) \/ x = an_error.
Proof.
  (* This time, we need to give a disjunctive pattern in [destruct]:
     - the first case is [some_nat] which takes one argument, let us call it [m]
     - the second case is [some_bool] with one argument, let us call it [b]
     - the final case has no argument, we leave it blank: *)
  destruct x as [m | b2 |] eqn:x_eq.
  - (* first case: [x = some_nat m] *)
    left. exists m. reflexivity.
  - (* second case: [x = some_bool b2] *)
    right. left. exists b2. reflexivity.
  - (* third case: [x = an_error] *)
    right. right. reflexivity.
Qed.

(** Exercise: prove the following lemma by case analysis. *)
Lemma nat_bool_error_not_nat_to_nat (x : nat_bool_error) :
  (forall (n : nat), x <> some_nat n) ->
  nat_bool_error_to_nat x = 0 \/ nat_bool_error_to_nat x = 1.
Proof.
Admitted. (* to be replaced with [Qed.] *)

(** ** Inductive inductive types *)

(** Of course, our previous [Inductive] types where not really inductive...
    Let us move on to types in which constructors may have arguments whose
    type is precisely the type being defined. *)

(** The most well-known (and useful) such type is [nat].
    It is already defined in the prelude. *)
Print nat.
Check O.
Check S.

(** As we see, it has two constructors:
    - O (the capital "o" letter) for the number 0
    - S, for the successor function, that is intuitively the function which
      returns its argument plus one.
    There are notations ([Number Notation]s in Rocq's terminology) to write
    - 0 (the number 0) instead of the constructor O (the "o" letter)
    - 1 instead of (S O)
    - 2 instead of (S (S O))
    - ...
*)
Check S (S O). (* prints 2 : nat *)
Check S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))). (* prints 13 : nat *)

(** For the moment, let us ignore the inductive nature of [nat].
    Everything we learned (case analysis, injectivity of the constructors, ...)
   still holds. *)

(** Exercise: prove the following lemma *)
Lemma neq_0_succ (n : nat) : 0 <> S n.
Proof.
Admitted. (* to be replaced with [Qed.] *)

(** Exercise: prove the following lemma *)
Lemma succ_inj (n m : nat) : S n = S m -> n = m.
Proof.
Admitted. (* to be replaced with [Qed.] *)

(** Now the predecessor function is our partial inverse for the [S]
    constructor. Arbitrarily, the predecessor of [0] is [0]. *)
Definition pred (n : nat) :=
  match n with
  | 0 => 0
  | S n => n
  end.

(** Exercise: prove the following lemma *)
Lemma pred_succ (n : nat) : pred (S n) = n.
Proof.
Admitted. (* to be replaced with [Qed.] *)

(** Exercise: prove the following lemma by case analysis. *)
Lemma succ_pred (n : nat) : n <> 0 -> S (pred n) = n.
Proof.
Admitted. (* to be replaced with [Qed.] *)

(** We can only do so much without recursion on [nat].
    Let us consider the following lemma: *)

Lemma neq_succ_diag_l (n : nat) : S n <> n.
Proof.
  (* Let us try a case analysis on [n]: *)
  destruct n as [| m].
  - (* first case: [n = 0] *)
    intros H. discriminate H.
  - intros H. injection H as H.
    (* It would be ok, if we knew that the predecessor [m] of [n] already
       satisfies the property [S m <> m].
       But we don't, case analysis is not sufficient. *)
Abort.

(** When we have an "inductive" [Inductive] such as [nat], we can reason
    by [induction] on a variable of this type.
    It is much like reasoning by case analysis, except that we may assume
    that the inductive arguments of the constructors already satisfy the
    property that is being proved. *)

Lemma neq_succ_diag_l (n : nat) : S n <> n.
Proof.
  (* We reason by induction on the variable [n]:
     - in the first case, [n = 0] and there is no variable (nor hypothesis)
       to introduce
     - in the second case, [n = S m] and [m] satisfies the hypothesis [IH] *)
  induction n as [| m IH].
  - (* first case: [n = 0] *)
    intros H. discriminate H.
  - intros H. injection H as H.
    apply IH. exact H.
Qed.

(** It should be intuitively clear that such a reasoning is valid.
    We have proved that 0 <> 1, and also that,
    if S m <> m, then S (S m) <> S m, so we get
    1 <> 2, then 2 <> 3, and so on.
    We hope to write a "Simple inductive types, behind the scenes" tutorial
    where we abandon all magic and show that, ultimately, it all comes down to
    the [match] construct. For the time being, we satisfy ourselves with this
    intuition. *)

(** In order to give more examples (and exercises!), let us introduce the
    addition on natural numbers. *)

Print Nat.add.
About "+". (* We can use the "+" infix notation for add *)

(** In other words, the addition is defined by the two rules:
    - 0 + m = m
    - (S p) + m = S (p + m)

    There is a big difference with our previous functions, however, as
    emphasized by the keyword [Fixpoint], which is a fancy way to say that our
    function is _recursive_, that is, may have to call itself to continue
    the computation.

    The two rules above are enough to compute. *)
Compute 2 + 3.
Compute 39 + 3.
(** It is important for the reader to convince herself that our [add] function
    does indeed terminate on every argument and produces a result.
    Here is how [Rocq] sees our [2 + 3] computation.
    First, [2 + 3] is actually [S (S O) + S (S (S O))]. Now,

    S (S O) + S (S (S O)) = S (S O + S (S (S O))), because the left
    operands matches (S p), with [p = S O]. Now,
    S (S O + S (S (S O))) = S (S (O + S (S (S O)))), for the same reason.
    Finally,
    S (S (O + S (S (S O)))) = (S (S (S (S (S O))))) = 5.
    
    It may not be very readable as a comment, so let us write down explicitly
    this computation in a proof.
    We need the two rewriting rules above. *)

Lemma add_0_l (m : nat) : 0 + m = m.
Proof. reflexivity. Qed.
Lemma add_succ_l (n m : nat) : (S n) + m = S (n + m).
Proof. reflexivity. Qed.

Lemma two_plus_three : 2 + 3 = 5.
Proof.
  rewrite add_succ_l.
  rewrite add_succ_l.
  rewrite add_0_l.
  reflexivity.
Qed.

(** Of course, [Rocq] would compute without us expliciting these rules... *)
Goal 2 + 3 = 5.
Proof. reflexivity. Qed.

(** If it was your first encounter with recursive functions, it is probably a
    lot to digest, let us see more examples. *)

Lemma add_0_r (n : nat) : n + 0 = n.
Proof. 
  (* this is not a result of computation, [simpl] will do nothing here. *)
  simpl.
  (* indeed, the definition of [add] knows how to deal with [0] as a left
     operand, not as a right operand.
     We could try reasoning by case analysis, but it would fail (you may try
     it yourself if you doubt it). *)
  induction n as [| m IH].
  - (* first case: n = 0 *)
    rewrite add_0_l. reflexivity.
  - (* second case: n = S m where m satisfies the induction hypothesis (IH): *)
    rewrite add_succ_l. 
    rewrite IH.
    reflexivity.
Qed.

(** Exercise: prove by induction the following lemma *)
Lemma add_succ_r (n m : nat) : n + S m = S (n + m).
Proof.
Admitted. (* to be replaced with [Qed.] *)

(** Exercise: prove by induction the following lemma *)
Lemma add_comm (n m : nat) : n + m = m + n.
Proof.
Admitted. (* to be replaced with [Qed.] *)

(** Exercise: prove by induction the following lemma *)
Lemma add_assoc (n m p : nat) : (n + m) + p = n + (m + p).
Proof.
Admitted. (* to be replaced with [Qed.] *)

(** From there, we could add a countable infinity of exercise, for instance
    about multiplication, ... Feel free to tell us if you feel that you
    need, or want more exercises! *)

(** *** Positive (binary) natural numbers *)

(** Natural numbers encoded with O and S are very nice to prove properties about
    natural numbers. Unfortunately, they are not so convenient for computations
    with large numbers. Here we define binary positive numbers. *)

Inductive positive :=
| xI (p : positive)
| xO (p : positive)
| xH.

(** A positive is either
    - [xH] which represents the value 1
    - appending the binary number 0 at the end of a positive (that is,
      multiplying it by 2)
    - appending the binary number 1 at the end of a positive (that is,
      multiplying it by 2 and adding 1). *)
Check xH.
Check xI.
Check xO.

(** The order of the "digits" may confuse you, it is the reversed order of
    what we are used to: here are the first natural numbers: *)
Check xH. (* 1 *)
Check xO xH. (* 10 in binary, 2 in decimal *)
Check xI xH. (* 11 in binary, 3 in decimal *)
Check xO (xO xH). (* 100 in binary, 4 in decimal *)
Check xI (xO xH). (* 101 in binary, 5 in decimal *)

(** Let us define the successor of such a number: *)
Fixpoint succ (p : positive) :=
  match p with
  | xH => xO xH
  | xI q => xO (succ q)
  | xO q => xI q
  end.

(** As you can see, there are now two recursive cases, because there are
    two recursive constructors in [positive]. *)

Compute succ xH.
Compute succ (succ xH).
Compute succ (succ (succ xH)).
Compute succ (succ (succ (succ xH))).

(** By case analysis, [succ p] is never equal to 1 (xH): *)
Lemma pos_succ_neq_1 (p : positive) : succ p <> xH.
Proof.
  destruct p as [q | q |]; intros H; discriminate H.
Qed.

(** Let us look at an example of proof by induction when there are two inductive
    steps. *)
Lemma pos_succ_inj : forall (p q : positive), succ p = succ q -> p = q.
Proof.
  induction p as [p' IHp' | q' IHq' |].
  - intros [q1 | q1 |].
    + intros [= ->%IHp']. reflexivity.
    + intros [= H].
    + intros [= []%pos_succ_neq_1].
  - intros [q1 | q1 |].
    + intros [= H].
    + intros [= ->]. reflexivity.
    + intros [= H].
  - intros [q1 | q1 |]; [intros [= H].. | intros _; reflexivity].
    apply eq_sym, pos_succ_neq_1 in H as [].
Qed.

(** TODO: more exercises *)

(** ** Parameterized inductive types *)

(** TODO: lists, maybe binary trees *)
