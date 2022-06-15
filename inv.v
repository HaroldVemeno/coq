Require Import Arith.

Theorem invert : forall a b : nat, a + a = b + b -> a = b.
Proof.
  induction a.
  intros.
  destruct b.
  easy.
  easy.
  intros.
  destruct b.
  easy.
  simpl in H.
  rewrite Nat.add_comm in H.
  simpl in H.
  symmetry in H.
  rewrite Nat.add_comm in H.
  simpl in H.
  injection H as H.
  f_equal.
  apply IHa.
  symmetry in H.
  exact H.
Qed.



Qed.
