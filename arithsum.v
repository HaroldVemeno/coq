From Coq Require Import Arith.
Require Import Arith.

Require Import Psatz.

Fixpoint div2 (n : nat) : nat :=
  match n with
    | 0 => 0
    | 1 => 0
    | S (S m) => S (div2 m)
  end.

Theorem div2_n: forall n k, div2 (2 * n + k) = n + div2 (k).
Proof.
  intros.
  induction n.
  - reflexivity.
  - rewrite Nat.mul_comm.
    simpl.
    rewrite Nat.mul_comm.
    rewrite IHn.
    reflexivity.
Qed.


Fixpoint arith_sum (n : nat) : nat :=
  match n with
  | 0 => 0
  | S m => n + arith_sum m
  end.

Definition arith_formula2 (n : nat) : nat := div2 (n * (n + 1)).


Definition arith_formula (n : nat) : nat := div2 (n * (n + 1)).

Theorem arith_eq (n : nat) : arith_formula n = arith_sum n.
Proof.
  intros.
  induction n.
    compute.
    reflexivity.
    unfold arith_formula.
    simpl arith_sum.
    rewrite <- IHn.
    simpl Nat.add.
    simpl Nat.mul.
    rewrite Nat.mul_comm.
    simpl Nat.mul.
    rewrite Nat.mul_comm.
    rewrite Nat.add_assoc.
    rewrite (Nat.add_comm n 1).
    simpl Nat.add.
    simpl div2.
    f_equal.
    unfold arith_formula.
    assert (forall x y : nat, div2 (x + x + y) = x + div2 (y)).
      intros x y.
      induction x.
        simpl.
        reflexivity.
        simpl Nat.add.
        rewrite (Nat.add_comm x (S x)).
        simpl Nat.add.
        simpl div2.
        f_equal.
        assumption.
    rewrite H.
    f_equal.
    f_equal.
    rewrite (Nat.add_comm n 1).
    simpl Nat.add.
    reflexivity.
    Show Proof.
Qed.

Theorem arith_eq2 : forall (n : nat), arith_formula n = arith_sum n.
Proof.
  intros n.
  induction n.
    compute.
    reflexivity.
    simpl arith_sum.
    rewrite <- IHn.
    unfold arith_formula.
    simpl Nat.mul.
    rewrite (Nat.add_comm n 1).
    simpl Nat.add.
    simpl div2.
    f_equal.
    rewrite Nat.mul_comm.
    simpl Nat.mul.
    rewrite Nat.add_assoc.
    assert (forall x y : nat, div2 (x + x + y) = x + div2 y).
      intros x y.
      induction x.
      simpl.
      reflexivity.
      simpl Nat.add.
      rewrite (Nat.add_comm x (S x)).
      simpl Nat.add.
      simpl div2.
      f_equal.
      assumption.
    rewrite H.
    f_equal. f_equal.
    rewrite (Nat.mul_comm n (S n)).
    simpl Nat.mul.
    reflexivity.
    Show Proof.
Qed.

Theorem arith_eq3 : forall (n : nat), arith_formula n = arith_sum n.
Proof.
  intros n.
  induction n.
  - compute.
    reflexivity.
  - simpl.
    rewrite <- IHn.
    unfold arith_formula.
    rewrite Nat.add_comm.
    simpl.
    rewrite Nat.mul_comm.
    simpl.
    pose proof div2_n n.
    simpl "*" in H.
    rewrite Nat.add_0_r in H.
    rewrite Nat.add_assoc.
    rewrite (H (n + n * n)).
    f_equal.
    f_equal.
    f_equal.
    symmetry.
    rewrite Nat.mul_comm.
    rewrite Nat.add_comm.
    simpl.
    reflexivity.
Qed.
(*
Theorem div2_formula : forall (x : nat), exists (y : nat), 2 * y = x * (x + 1).
Proof.
  intros x.
  induction x.
    exists 0.
    simpl.
    reflexivity.
    simpl Nat.mul.
    rewrite (Nat.add_comm x 1).
    simpl Nat.add.
    rewrite (Nat.mul_comm x (S (S x))).
    simpl Nat.mul.
    simpl Nat.add.
    assert (p : nat).
      trivial.
    exists (x + (S p)).
    simpl Nat.add.
    rewrite Nat.add_comm.
    rewrite (Nat.add_comm x (S p)).
    simpl Nat.add.
    rewrite Nat.add_comm.
    simpl Nat.add.
    f_equal.
    f_equal.
    rewrite (Nat.add_comm p x).
    destruct IHx as [h H].
    simpl Nat.mul in H.
    rewrite (Nat.add_comm x 1) in H.
    simpl Nat.mul in H.
    rewrite Nat.mul_comm in H.
    simpl in H .
    rewrite <- H.
    rewrite (Nat.add_comm h 0).
    rewrite (Nat.add_comm).
    rewrite (Nat.add_comm (x + p) 0).
    simpl Nat.add.
    repeat rewrite Nat.add_assoc.
*)


Theorem div2_formula : forall (x : nat), exists (y : nat), 2 * y = x * (x + 1).
Proof.
  intros.
  assert (forall a : nat, exists b : nat, (a = 2 * b) \/ (S a = 2 * b)).
    intros.
    induction a.
    simpl.
    exists 0.
    left.
    simpl.
    reflexivity.
    destruct IHa as [b' H].
    destruct H as [H | H].
    exists (S b').
    right.
    rewrite (Nat.mul_comm).
    simpl Nat.mul.
    rewrite (Nat.mul_comm).
    rewrite <- H.
    reflexivity.
    exists b'.
    left.
    assumption.
  destruct (H x) as [b e].
  destruct e as [e | e].
    rewrite e.
    exists (b * (2 * b + 1)).
    rewrite Nat.mul_assoc.
    reflexivity.
    rewrite (Nat.add_comm).
    simpl Nat.add.
    rewrite e.
    rewrite (Nat.mul_comm).
    exists (b * x).
    rewrite Nat.mul_assoc.
    reflexivity.
  Show Proof.
Qed.

Theorem inducted_div2 (x y : nat) : div2 (2 * x + y) = x + div2 (y).
Proof.
  induction x.
    simpl.
    reflexivity.
    simpl Nat.add.
    rewrite (Nat.add_comm x 0).
    simpl Nat.add.
    rewrite (Nat.add_comm x (S x)).
    simpl Nat.add.
    simpl div2.
    f_equal.
    assert (x + x = 2 * x).
    simpl.
    rewrite (Nat.add_comm x 0).
    simpl.
    reflexivity.
    rewrite H.
    assumption.
Qed.

Definition even n := exists y,     2 * y = n.
Definition odd  n := exists y, 1 + 2 * y = n.

Theorem even_div2 (n : nat) : even n -> 2 * div2 n = n.
Proof.
  intros.
  unfold even in H.
  destruct H.
  rewrite <- H.
  assert (2 * x = 2 * x + 0); auto.
  rewrite H0 at 1.
  rewrite (inducted_div2 x).
  simpl div2.
  simpl.
  rewrite (Nat.add_comm x 0).
  simpl.
  rewrite (Nat.add_comm x 0).
  simpl.
  reflexivity.
Qed.
