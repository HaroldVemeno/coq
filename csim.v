Require Import Nat PeanoNat.

Definition PredTh := forall n m, n <= m -> pred n <= pred m.

Theorem predTh : PredTh.
Proof.
  unfold PredTh.
  induction n.
  - intros m H.
    exact (le_0_n _).
  - intros [] H; simpl.
    + exfalso.
      exact (Nat.nle_succ_0 _ H).
    + apply le_S_n.
      exact H.
Qed.

Require Import ssreflect.

Theorem predTh2 : PredTh.
Proof.
  elim=> [ |n IHn] m H /=.
  - by apply: le_0_n.
  - case: m H => [| m] H /=.
    + by case: (Nat.nle_succ_0 _ H).
    + exact (le_S_n _ _ H).
Qed.
