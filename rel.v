From Coq Require Import Relations.

Definition bad_theorem : Prop := forall (A : Type) (R : relation A),
  symmetric _ R ->
  transitive _ R ->
  reflexive _ R.

Variant em := emel.

Variant emr : relation em :=.

Theorem correct_version: ~bad_theorem.
Proof.
  intro bt.
  hnf in bt.
  unfold symmetric, transitive, reflexive in bt.
  specialize (bt em emr).
  assert (symmetric em emr).
  hnf.
  intros [] []; auto.
  assert (transitive em emr).
  hnf.
  intros [] [] [] a b; auto.
  specialize (bt H H0).
  specialize (bt emel).
  destruct bt.
Qed.
