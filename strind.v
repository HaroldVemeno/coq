Require Import ssreflect Nat PeanoNat Le Logic Lia.

Open Scope nat_scope.

Theorem nat_strong_ind : forall P : nat -> Prop,
P 0 -> (forall n, (forall k, k <= n -> P k) -> P (S n)) -> forall n, P n.
Proof.
  move=> P P0 SI n.
  assert (exists k, n <= k); first by exists n.
  case: H => k.
  move: n.
  induction k.
  - move=> n Le.
    destruct n.
    + exact P0.
    + lia.
  - move=> n H.
    apply Nat.lt_eq_cases in H.
    case: H => H.
    + apply IHk.
      lia.
    + rewrite H.
      apply SI => x.
      apply IHk.
Qed.

Theorem nat_strong2_ind : forall P : nat -> Prop,
(forall n, (forall k, k < n -> P k) -> P n) -> forall n, P n.
Proof.
  move=> P SI n.
  refine (nat_strong_ind P _ _ n).
  - apply: SI.
    move=> k Lt.
    inversion Lt.
  - move=> m OSI.
    apply: SI.
    move=> k Lt.
    apply: OSI.
    lia.
Qed.

Theorem nat_even_odd_ind : forall P : nat -> Prop,
P 0 -> P 1 -> (forall n , P n -> P (2 + n)) -> forall n, P n.
Proof.
  move=> P P0 P1 IH.
  fix H 1.
  case=> [|[|n]]; [exact: P0|exact: P1| ].
  apply: IH.
  apply: H.
  Show Proof.
Qed.

Theorem nat_my_ind : forall P : nat -> Prop,
P 0 -> (forall n , P n -> P (S n)) -> forall n, P n.
Proof.
  move=> P P0 IH.
  fix H 1.
  case=> [|n]; [exact: P0| ].
  apply: IH.
  apply: H.
Qed.

Fixpoint nat_my_def_ind (P : nat -> Prop)
    (p0 : P 0) (ih : (forall n, P n -> P (S n))) (n : nat) : P n :=
  match n with
    | 0 => p0
    | (S m) => ih m (nat_my_def_ind P p0 ih m)
  end.


Theorem even_odd_dec n: exists m, n = m * 2 \/ n = 1 + m * 2.
Proof.
  elim/nat_even_odd_ind: n => [ | | n H]; try exists 0; lia.
  case: H => [m [-> | ->]]; by exists (m + 1); lia.
Qed.

Theorem name : forall A B C : Prop, ((A -> B) /\ (A -> C)) <-> (A -> B /\ C).
Proof.
  move=> A B C.
  split.
  - move=> [ab ac] a.
    split.
    + exact (ab a).
    + exact (ac a).
  - move=> abc.
    split.
    + move=> a.
      move: (abc a) => [b c].
      exact b.
    + move=> a.
      move: (abc a) => [b c].
      exact c.
Qed.

Theorem nat_doubling_ind : forall P : nat -> Prop,
  P 0 -> (forall a : nat, P a -> (P (a * 2) /\ P (1 + a * 2))) -> forall n, P n .
Proof.
  move=> P P0 IH n.
  move: (IH 0 P0) => [_ P1] /=.
  simpl in P1.
  elim/nat_strong_ind: n => [| n SIH] //.
  case: (even_odd_dec n) => [m [E | E]];
  rewrite E.
  - case/name: (IH m) => m2m m2sm.
    apply: m2sm.
    apply: SIH.
    lia.
  - case/name: (IH (S m)) => m2m m2sm.
    apply: m2m.
    apply: SIH.
    lia.
Qed.

Theorem nat_doube_ind : forall R : nat -> nat -> Prop,
  (forall n, R 0 n) -> (forall n, R (S n) 0) ->
  (forall n m, R n m -> R (S n) (S m)) ->
  forall n m, R n m.
Proof.
  move=> R R0n Rn0 RS.
  fix IH 1 => n m.
  case: n => [| n0]; first exact: R0n.
  case: m => [| m0]; first exact: Rn0.
  apply: RS.
  exact: IH.
Qed.
