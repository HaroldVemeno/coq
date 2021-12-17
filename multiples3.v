Require Import PeanoNat.
Inductive multiple_of_3 : nat -> Prop :=
  | O_multiple : multiple_of_3 O
  | SSS_multiple n (H : multiple_of_3 n) : multiple_of_3 (S (S (S n))).

Inductive multiple_of_3' : nat -> Prop :=
  | thirty_multiple : multiple_of_3' 30
  | twenty_one_multiple : multiple_of_3' 21
  | sum_multiple n m (H : multiple_of_3' n) (H' : multiple_of_3' m) : multiple_of_3' (n + m)
  | difference_multiple l n m (H : multiple_of_3' n) (H' : multiple_of_3' m) (H'' : l + n = m) : multiple_of_3' l.

Lemma zero' : multiple_of_3' 0.
  Proof.
    apply (difference_multiple 0 21 21).
    apply twenty_one_multiple.
    apply twenty_one_multiple.
    simpl.
    reflexivity.
    Qed.

Lemma three' : multiple_of_3' 3.
  Proof.
    apply (difference_multiple 3 9 12).
    apply (difference_multiple 9 21 30).
    constructor.
    constructor.
    simpl.
    reflexivity.
    apply (difference_multiple 12 9 21).
    apply (difference_multiple 9 21 30).
    constructor.
    constructor.
    simpl.
    reflexivity.
    constructor.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
  Qed.

Lemma all' : forall n : nat, multiple_of_3' n -> multiple_of_3' (S (S (S n))).
  Proof.
    intros.
    assert (forall x : nat, S (S (S x)) = x + 3).
      intro.
      rewrite Nat.add_comm.
      unfold "+".
      reflexivity.
    rewrite H0.
    apply (sum_multiple n 3).
    assumption.
    apply three'.
Qed.

Theorem multiple_of_3_iff_multiple_of_3' :
  forall n, multiple_of_3 n <-> multiple_of_3' n.
Proof.
  intros.
  split.
  intros.
  induction H.
  apply zero'.
  apply (sum_multiple _ _ three' IHmultiple_of_3).
  intros.
  induction H.
  repeat constructor.
  repeat constructor.
  induction IHmultiple_of_3'1.
  simpl.
  exact IHmultiple_of_3'2.
  simpl.
  constructor.
  apply IHIHmultiple_of_3'1.
  refine (difference_multiple n 3 (S (S (S n))) three' H _).
  rewrite Nat.add_comm.
  simpl.
  reflexivity.
  generalize dependent m.
  generalize dependent l.
  intros.


Qed.
