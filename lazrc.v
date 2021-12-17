Require Import Basics PeanoNat Bool.
Require Import Lia ZifyBool.

Inductive List : Set :=
  | nil : List
  | cons (n : nat) (tail : List) : List.


Fixpoint length (l : List) : nat := match l with
  | nil => 0
  | cons _ rest => 1 + length rest
  end.

Fixpoint count (n : nat) (l : List) : nat :=
  match l with
  | nil => 0
  | cons m lr => (if m =? n then 1 else 0) + count n lr
  end.

Fixpoint push (a : nat) (l : List) : List :=
  match l with
  | nil => cons a nil
  | cons h rest => cons h (push a rest)
  end.

Fixpoint reverse (a : List) : List :=
  match a with
  | nil => nil
  | cons a rest => push a (reverse rest)
  end.

Notation "a +> b" := (cons a b) (right associativity, at level 30).
Notation "[]" := nil.
Notation "[ a ; .. ; e ]" := ( cons a .. (cons e nil) ..).

Fixpoint append (a b : List) : List :=
  match a with
  | [] => b
  | a +> ar => a +> append ar b
  end.

Notation "a ++ b" := (append a b).
Notation "a <+ b" := (push b a) (left associativity, at level 31).

Inductive Sorted (R : nat -> nat -> Prop): List -> Prop :=
  | Sorted_empty : Sorted R nil
    (* prázdný List je vždy seřazen *)
  | Sorted_one (n : nat) : Sorted R (cons n nil)
    (* List s jedním prvkem je také vždy seřazen *)
  | Sorted_cons (n : nat) (m : nat) (rest : List)
    (* List s více prvky [n, m, ...rest] je seřazen, když:*)
      (* 1. n a m jsou správně seřazeny: *)
        (first_pair_sorted : R n m)
      (* 2. zbytek [m, ...rest] je seřazen: *)
        (rest_sorted : Sorted R (cons m rest))
      : Sorted R (cons n (cons m rest)).

Notation LeSorted := (Sorted le).

Theorem Sorted_tail {l a R}: Sorted R (cons a l) -> Sorted R l.
Proof.
  intros.
  inversion H.
  - constructor.
  - apply rest_sorted.
Qed.

Theorem Sorted_append {R l1 n l2 m} :
  Sorted R (push n l1) ->
  Sorted R (cons m l2) ->
  R n m
  -> Sorted R (append (push n l1) (cons m l2)).
Proof.
  generalize dependent l2.
  generalize dependent m.
  generalize dependent n.
  induction l1; intros.
  - simpl.
    constructor.
    exact H1.
    exact H0.
  - simpl in *.
    pose proof (Sorted_tail H).
    pose proof (IHl1 _ _ _ H2 H0 H1).
    destruct l1.
    + simpl in *.
      inversion H. subst.
      repeat assumption || constructor.
    + simpl in *.
      inversion H; subst.
      constructor.
      exact first_pair_sorted.
      exact H3.
Qed.

Inductive Elem (n: nat) : List -> Prop :=
  | Elem_triv : forall l, Elem n (n +> l)
  | Elem_cons : forall l u, Elem n l -> Elem n (u +> l).

Notation "a ∈ b" := (Elem a b) (at level 70, no associativity).

Check 5 ∈ [2; 5; 6].

Goal 5 ∈ [2; 5; 6].
  auto using Elem.
  Show Proof.
Qed.


Theorem Elem_tail {l n u}: n ∈ (u +> l) -> n <> u -> n ∈ l.
Proof.
  intros.
  inversion H; subst.
  - contradiction.
  - assumption.
Qed.

Theorem Elem_push l n: Elem n (push n l).
Proof.
  induction l.
  - constructor.
  - simpl.
    constructor.
    exact IHl.
Qed.

Theorem List_push_case l: l = nil \/ exists n r, l = push n r.
Proof.
  induction l.
  - left. reflexivity.
  - right.
    destruct IHl.
    + rewrite H.
      exists n.
      exists [].
      simpl.
      reflexivity.
    + destruct H as (m & r & H).
      rewrite H.
      exists m.
      exists (n +> r).
      simpl.
      reflexivity.
Qed.

Theorem count_append a b : forall n, count n (a ++ b) = count n a + count n b.
Proof.
  generalize dependent b.
  induction a; intros.
  - simpl.
    reflexivity.
  - simpl.
    destruct (Nat.eqb_spec n n0).
    + simpl.
      f_equal.
      apply IHa.
    + simpl.
      apply IHa.
Qed.

Theorem count_elem n l: count n l >= 1 <-> Elem n l.
  split.
  - intros.
    induction l.
    + simpl in H.
      lia.
    + simpl in *.
      destruct (Nat.eqb_spec n0 n).
      * subst.
        constructor.
      * simpl in H.
        specialize (IHl H).
        constructor.
        exact IHl.
  - intros.
    induction l.
    + inversion H.
    + simpl in *.
      inversion H; subst.
      * rewrite Nat.eqb_refl.
        lia.
      * pose proof (IHl H1).
        lia.
Qed.

Fixpoint filter (f: nat -> bool) (l: List): List :=
  match l with
  | nil => nil
  | cons n r => if f n then cons n (filter f r)
                      else filter f r
  end.

Theorem filter_forall l f: forall n, Elem n (filter f l) -> Elem n l /\ f n = true.
Proof.
  intros.
  generalize dependent n.
  induction l.
  - intros.
    simpl in H.
    inversion H.
  - intros.
    simpl in H.
    destruct (f n) eqn:E.
    + inversion H; subst.
      * split.
        -- constructor.
        -- exact E.
      * split.
        constructor.
        -- apply IHl.
           exact H1.
        -- apply IHl.
           exact H1.
    + specialize (IHl n0 H).
      destruct IHl.
      split.
      * constructor.
        exact H0.
      * exact H1.
Qed.

Theorem filter_length f l: length (filter f l) <= length l.
  induction l.
  - simpl.
    lia.
  - simpl.
    destruct (f n).
    + simpl.
      lia.
    + lia.
Qed.

Definition Permutation a b : Prop := forall n, count n a = count n b.

Theorem Permutation_symm {l r}: Permutation l r -> Permutation r l.
Proof.
  intros P n.
  specialize (P n).
  rewrite P.
  reflexivity.
Qed.

Theorem Permutation_Elem {l l'}: Permutation l l' -> forall n, Elem n l -> Elem n l'.
Proof.
  intros.
  unfold Permutation in H.
  rewrite <- count_elem in *.
  specialize (H n).
  rewrite <- H.
  exact H0.
Qed.

Require Import FunInd Recdef.

Function fquicksort (l : List) {measure length l} : List :=
  match l with
  | [] => []
  | p +> r => (fquicksort (filter (fun a => a <? p) r)) ++ ( p +> (fquicksort (filter (fun a => p <=? a) r)))
  end.
Proof.
  all: intros.

  remember (fun a => p <=? a) as more.
  pose proof (filter_length more r).
  simpl. lia.

  remember (fun a => a <? p) as less.
  pose proof (filter_length less r).
  simpl. lia.
Defined.

Theorem fquicksort_permutation l: Permutation l (fquicksort l).
Proof.
  intros n.
  functional induction (fquicksort l) as [ | ? p r ? IHbefore IHafter].
  - simpl. reflexivity.
  - set (less := fun a => a <? p) in *.
    set (before := filter less r) in *.
    set (more := fun a => p <=? a) in *.
    set (after := filter more r) in *.
    simpl.
    rewrite count_append.
    simpl.
    enough (count n r = count n (fquicksort before) + count n (fquicksort after))
      by (simpl;lia).
    destruct IHbefore, IHafter.
    induction r.
    + simpl. reflexivity.
    + subst less more before after.
      simpl in *.
      destruct (n0 <? p) eqn:E.
      * replace (p <=? n0) with false by lia.
        simpl. lia.
      * replace (p <=? n0) with true by lia.
        simpl. lia.
Qed.

Theorem fquicksort_sorted l: LeSorted (fquicksort l).
Proof.
  functional induction (fquicksort l) as [ | ? p l ? IHbefore IHafter].
  - constructor.
  - set (less := fun a => a <? p) in *.
    set (before := filter less l) in *.
    set (more := fun a => p <=? a) in *.
    set (after := filter more l) in *.

    assert ( LeSorted (cons p (fquicksort after))) as p_after_sorted. {
      clear IHbefore less before.
      remember (fquicksort after) as qafter.
      destruct qafter.
      + constructor.
      + constructor.
        rewrite Heqqafter in *.
        pose proof (fquicksort_permutation after).
        apply Permutation_symm in H.
        pose proof (Permutation_Elem H n).
        assert (Elem n (n +> qafter)) by constructor.
        rewrite Heqqafter in H1.
        apply H0 in H1.
        clear H0 H qafter Heqqafter.
        subst more after.
        apply filter_forall in H1.
        destruct H1.
        lia.
        exact IHafter.
    }


    destruct (List_push_case (fquicksort before)) as [-> | H].
    + simpl.
      exact p_after_sorted.
    + destruct H as (n & r & push_eq).
      rewrite push_eq.
      apply Sorted_append.
      * rewrite <- push_eq.
        exact IHbefore.
      * exact p_after_sorted.
      * clear p_after_sorted more after IHafter.
        pose proof (fquicksort_permutation before).
        apply Permutation_symm in H.
        pose proof (Permutation_Elem H n).
        pose proof (Elem_push r n).
        rewrite <- push_eq in H1.
        apply H0 in H1.
        clear push_eq H0 H r.
        subst before less.
        apply filter_forall in H1.
        destruct H1.
        lia.
Qed.


Definition fquicksort_spec: forall l, Permutation l (fquicksort l) /\ LeSorted (fquicksort l) :=
  fun l => conj (fquicksort_permutation l) (fquicksort_sorted l).
