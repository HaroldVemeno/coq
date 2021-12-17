(* The following lemma from Div2 is useful:
   ind_0_1_SS : forall P : nat -> Prop,
      P 0 -> P 1 ->
        (forall n : nat, P n -> P (S (S n))) ->
          forall n : nat, P n *)

From Coq Require Import Arith Div2 Lia PeanoNat.

Fixpoint div_mod2 (n : nat) : (nat * bool) :=
  match n with
  | 0 => (0, false)
  | 1 => (0, true)
  | S (S n) => let (a, b) := div_mod2 n in (S a, b)
  end.

Lemma dd n: exists m,  n = 2 * m \/ n = 1 + 2 * m.
Proof.
  intros.
  induction n.
  exists 0.
  lia.
  destruct IHn.
  destruct H.
  exists x.
  lia.
  exists (S x).
  lia.
Qed.

Lemma div_spec1 n: div_mod2(2 * n) = (n, false).
Proof.
  induction n.
  easy.
  simpl.
  replace (n + S (n + 0)) with (S (2 * n)) by lia.
  rewrite IHn.
  easy.
Qed.

Lemma div_spec2 n: div_mod2(1 + 2 * n) = (n, true).
Proof.
  induction n.
  easy.
  simpl.
  replace (n + S (n + 0)) with (1 + 2 * n) by lia.
  rewrite IHn.
  easy.
Qed.

Lemma dind: forall (P : nat -> Prop),
    P 0 ->
    (forall n, P n ->  P (2 * n)) ->
    (forall n, P n -> P (1 + 2 * n))
    -> forall n, P n.
Proof.
  intros P P0 P2 PS2 n.
  induction n using lt_wf_ind.
  destruct (dd n) as [m [Hd | Hd]]; subst.
  destruct m.
  simpl.
  exact P0.
  apply P2.
  apply H.
  lia.
  apply PS2.
  apply H.
  lia.
Qed.

Fixpoint pow_sqr_aux (k b e : nat) : nat :=
  match k, e with
  | 0, _ => 1
  | _, 0 => 1
  | S k, _ => match div_mod2 e with
              | (e', false) => pow_sqr_aux k (b * b) e'
              | (e', true) => b * pow_sqr_aux k (b * b) e'
              end
  end.

Definition pow_sqr (b e : nat) : nat := pow_sqr_aux e b e.

Theorem pow_eq (b e : nat) : pow_sqr b e = b ^ e.
Proof.
  revert b.
  induction e using dind; intros.
  reflexivity.
  unfold pow_sqr, pow_sqr_aux.
  destruct e.
  simpl.
  reflexivity.
  replace (2 * S e) with (S (S (2 * e))) by lia.
  replace (S (S (2 * e))) with (2 * S e) by lia.
  rewrite div_spec1.
  destruct (div_mod2 (S e)).
  destruct b0.
  replace (e + S (e + 0)) with (1 + 2 * e) by lia.
