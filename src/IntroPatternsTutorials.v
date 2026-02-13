(** * (Default) Intro Patterns Tutorials

    *** Summary

    This tutorial is about (default) intro patterns we can use in a proof
    with default Coq tactics. Intro Patterns help gain a lot of time during
    proofs writing and make the proofs more natural to read and write.
    Once used to intro patterns, you can't live without it!

    *** Prerequisites

    Needed:
    - The user should already have some very minimal Coq experience with proof
      writing.

    Installation:
    This tutorial should work for Coq V8.17 or later.
*)

Lemma disjunctive_pattern (A B : Prop) : A \/ B -> B \/ A.
Proof.
  (* disjunctive pattern *)
  intros [H | H'].
  - right; exact H.
  - left; exact H'.
Qed.

Lemma cunjunctive_pattern (A B : Prop) : A /\ B -> B /\ A.
Proof.
  (* conjunctive pattern *)
  intros [H H'].
  split.
  - exact H'.
  - exact H.
Qed.

Lemma throwing_away (A B : Prop) : A /\ B -> A.
Proof.
  (* useless parts can be thrown away *)
  intros [H _].
  exact H.
Qed.

Lemma nested_intro_pat (A B C : Prop) : A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).
Proof.
  (* intro patterns can be nested *)
  intros [HA [HB | HC]].
  - left. split.
    + exact HA.
    + exact HB.
  - right. split.
    + exact HA.
    + exact HC.
Qed.

Lemma arrow_intro_pat (x : nat) : x = 0 -> x + x = x.
Proof.
  (* the -> intro pattern acts like "rewrite name; clear name" *)
  intros ->. reflexivity.
Qed.

Lemma apply_in_intro_pat (x : nat) : x = 0 -> x = x + x.
Proof.
  (* the hyp%term intro pattern acts like "intros hyp; apply term in hyp" *)
  intros Hx%arrow_intro_pat. symmetry. exact Hx.
Qed.

Lemma composition_of_apply_in (x : nat) : x = 0 -> x = x + x.
Proof.
  (* % intro patterns can be composed *)
  intros Hx%arrow_intro_pat%eq_sym. exact Hx.
Qed.

Lemma intro_pat_following_as (A B : Prop) : A -> B -> A /\ B.
Proof.
  intros H1 H2.
  (* intro patterns can occur (almost) every time you name a term.
     assert ([H H']: A /\ B) fails but this works: *)
  assert (A /\ B) as [H H'].
  (* this was an artificial example *)
  easy. easy.
Qed.
