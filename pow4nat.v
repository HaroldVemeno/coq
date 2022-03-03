From Coq Require Import PeanoNat Lia.

Theorem a_pow_4_sub_b_pow_4 : forall a b,
  a ^ 4 - b ^ 4 = (a - b) * (a + b) * (a ^ 2 + b ^ 2).
Proof.
  intros.
  assert (a <= b \/ a > b) by lia.
  destruct H.
  rewrite <- Nat.sub_0_le in H.
  enough (a ^ 4 - b ^ 4 = 0) by lia.
  rewrite Nat.sub_0_le in H.
  assert (a ^ 4 <= b ^ 4).
  simpl.
  enough (a * a <= b * b) by nia.
  nia.
  rewrite Nat.sub_0_le.
  exact H0.
  assert ((a - b) * (a + b) = a * a - b * b) by nia.
  rewrite H0.
  simpl.
  nia.
Qed.
