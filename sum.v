From Coq Require Import Arith Lia.

Fixpoint sum_simple (f : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => f 0
  | S m => f n + sum_simple f m
  end.

Fixpoint sum_aux (a : nat) (f : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => f 0 + a
  | S m => sum_aux (f n + a) f m
  end.

Definition sum_tail := sum_aux 0.

Lemma sum_aux_a a f n: sum_aux a f n = a + sum_tail f n.
Proof.
  revert a f.
  induction n.
  intros.
  cbn.
  lia.
  intros.
  cbn.
  rewrite Nat.add_0_r.
  do 2 rewrite IHn.
  lia.
Qed.

Theorem sum_eq (f : nat -> nat) (n : nat) : sum_tail f n = sum_simple f n.
Proof.
  induction n.
  compute.
  induction (f 0).
  reflexivity.
  lia.
  cbn.
  rewrite sum_aux_a.
  rewrite IHn.
  lia.
Qed.
