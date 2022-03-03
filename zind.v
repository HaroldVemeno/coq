From Coq Require Import ZArith Lia.

Open Scope Z.

Theorem int_induction : forall (P : Z -> Prop) (m : Z),
  (forall n, n <= m -> P n) ->
  (forall n, m <= n -> P n -> P (Z.succ n)) ->
  forall n, P n.
Proof.
  intros.
  destruct n, m.
  destruct (Z.le_gt_cases n m).
  specialize (H _ H1).
  exact H.
  assert ( m <= Z.pred n) by lia.
  specialize (H0 _ H2).
  replace (Z.succ (Z.pred n)) with n in H0 by lia.
  apply H0.

Close Scope Z.
