(* The following lemma from Div2 is useful:
   ind_0_1_SS : forall P : nat -> Prop,
      P 0 -> P 1 -> 
        (forall n : nat, P n -> P (S (S n))) -> 
          forall n : nat, P n *)
From Coq Require Import Arith Div2.

Fixpoint div_mod2 (n : nat) : (nat * bool) :=
  match n with
  | 0 => (0, false)
  | 1 => (0, true)
  | S (S n) => let (a, b) := div_mod2 n in (S a, b)
  end.

Fixpoint div2 (n : nat) : nat := 
    match n with 
    | 0 => 0
    | 1 => 0
    | S (S n) => S (div2 n)
    end.

Fixpoint mod2 (n : nat) : bool := 
    match n with 
    | 0 => false
    | 1 => true
    | S (S n) => mod2 n
    end.

Theorem ddmm : forall (n : nat), div_mod2 n = (div2 n, mod2 n).
Proof.
    intros.
    induction n using ind_0_1_SS.
    compute. reflexivity.
    compute. reflexivity.
    simpl.
    rewrite IHn.
    reflexivity.
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

Theorem S_k : forall (k b e e': nat), pow_sqr_aux e b e' = pow_sqr_aux (e + k) b e'.
Proof.
    intros.
    generalize dependent k.
    generalize dependent b.
    generalize dependent e.
    induction e'.
    intros.
    simpl.
    unfold pow_sqr_aux.
    case k.
    rewrite Nat.add_comm.
    simpl "+".
    reflexivity.
    reflexivity.
    intros.
    simpl.


Theorem pow_eq (b e : nat) : pow_sqr b e = b ^ e.
Proof.
    generalize dependent b.
    induction e using ind_0_1_SS; intro.
    compute. reflexivity.
    compute. reflexivity.
    simpl.
    unfold pow_sqr in *.
    unfold pow_sqr_aux in *.
    fold pow_sqr_aux in *.
    rewrite ddmm.
    rewrite ddmm.
    simpl.


    rewrite -> (IHe (b * b * (b * b))).