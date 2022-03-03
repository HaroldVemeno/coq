Require Import List Arith.
Import ListNotations.

Inductive Subseq : list nat -> list nat -> Prop :=
| Subseq_nil : Subseq [] []
| Subseq_take : forall a xs ys, Subseq xs ys -> Subseq (a :: xs) (a :: ys)
| Subseq_drop : forall a xs ys, Subseq xs ys -> Subseq xs (a :: ys).

Fixpoint subseq_match (xs ys : list nat) : bool :=
  match xs with
  | [] => true
  | x :: xs' =>
    (fix go (us : list nat) :=
      match us with
      | [] => false
      | u :: us' =>
          if x =? u
          then subseq_match xs' us'
          else go us'
      end) ys
  end.

Theorem subseq_match_take xs ys a: subseq_match xs ys = subseq_match (a :: xs) (a :: ys).
Proof.
  simpl.
  rewrite (Nat.eqb_refl).
  easy.
Qed.

Theorem subseq_match_drop xs ys a: subseq_match xs ys = true -> subseq_match xs (a :: ys) = true.
Proof.
  intros.
  revert dependent ys.
  revert dependent a.
  induction xs; [easy| ]; intros.
  simpl in *.
  destruct (Nat.eqb_spec a a0); subst.
  destruct ys; [easy | ].
  destruct (Nat.eqb_spec a0 n); subst.
  apply IHxs.
  exact H.
  apply IHxs.
  destruct ys.
  easy.




Qed.

Theorem subseq_match_correct : forall (xs ys : list nat),
  subseq_match xs ys = true <-> Subseq xs ys.
Proof.
  intros.
  generalize dependent xs.
  induction ys; intros; split; intros.
    - destruct xs.
      + constructor.
      + simpl in H.
        discriminate.
    - inversion H. simpl. easy.
    - destruct xs.
      + constructor.
        apply IHys.
        simpl.
        easy.
      + simpl in H.
        destruct (Nat.eqb_spec n a); subst.
        * constructor.
          apply IHys.
          exact H.
        * constructor.
          apply IHys.
          exact H.
    - destruct xs.
      + simpl. easy.
      + inversion H; subst.
        simpl.
        rewrite (Nat.eqb_refl a).
        apply IHys.
        exact H1.
        apply IHys in H2.
        simpl.
        destruct (Nat.eqb_spec n a); subst.
