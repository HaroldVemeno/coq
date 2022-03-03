Require Import Reals Lra Lia.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | S (S n as n') => fib n' + fib n
  end.

Arguments fib : simpl nomatch.

Definition phi := ((1 + sqrt 5) / 2)%R.

Definition psi := ((1 - sqrt 5) / 2)%R.

Open Scope R_scope.

Definition pfib (n : nat) : R := (phi ^ n - psi ^ n) / sqrt 5.

Lemma sqrt5n0 : sqrt 5 <> 0.
Proof.
  assert (0 < 5) by lra.
  pose proof (sqrt_lt_R0 5 H).
  lra.
Qed.

Theorem pfib_s (n : nat) : pfib n + pfib (S n) = pfib (S (S n)).
Proof.
  unfold pfib, phi, psi.
  field_simplify_eq.
  simpl in *.
  field_simplify_eq.
  replace (sqrt 5 ^ 2) with 5 in *.
  lra.
  assert (0 <= 5) by lra.
  pose proof (Rsqr_sqrt 5 H).
  unfold Rsqr in H0.
  lra.
  exact sqrt5n0.
Qed.

Theorem binet : forall n, INR (fib n) = (phi ^ n - psi ^ n) / sqrt 5.
Proof.
  intros.
  enough (INR (fib n) = pfib n) by (unfold pfib in *; congruence).
  pose proof sqrt5n0.
  induction n using lt_wf_ind.
  destruct n as [|[]].
  unfold pfib.
  simpl. lra.
  unfold pfib, phi, psi.
  simpl. field. easy.
  rewrite <- pfib_s.
  simpl.
  rewrite plus_INR.
  rewrite (H0 n ltac:(lia)).
  rewrite (H0 (S n) ltac:(lia)).
  lra.
Qed.
