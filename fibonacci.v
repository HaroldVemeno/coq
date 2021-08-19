From Coq Require Import Arith.


Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | S (S n as n') => fib n' + fib n
  end.

Fixpoint fib_aux (a b n : nat) : nat :=
  match n with
  | 0 => a
  | S n => fib_aux b (a + b) n
  end.

Definition fib2 (n : nat) : nat := fib_aux 0 1 n.


Theorem fib_eq (n : nat) : fib2 n = fib n.
Proof.
  intros.
  induction n.
  trivial.
  unfold fib2.
  assert (forall m a b, fib_aux a b (S m) = a * fib m + fib (S m) * b ).
    induction m.
    intros.
    simpl.
    simpl Nat.mul.
    rewrite (Nat.mul_comm a 0).
    simpl Nat.mul.
    simpl Nat.add.
    rewrite (Nat.add_comm b 0).
    simpl Nat.add.
    reflexivity.
    simpl in *.
    intros.
    rewrite IHm.
    ring.
  rewrite (H n 0 1).
  ring.
Qed.
