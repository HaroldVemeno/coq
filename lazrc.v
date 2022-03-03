Require Import Basics PeanoNat Bool Arith Nat.
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

Declare Scope List_scope.
Delimit Scope List_scope with List.

Notation "a +> b" := (cons a b) (right associativity, at level 30) : List_scope.
Notation "[ ]" := nil : List_scope.
Notation "[ a ; .. ; e ]" := ( cons a .. (cons e nil) ..) : List_scope.

Open Scope List_scope.

Fixpoint append (a b : List) : List :=
  match a with
  | [] => b
  | a +> ar => a +> append ar b
  end.

Notation "a ++ b" := (append a b) : List_scope.
Notation "a <+ b" := (push b a) (left associativity, at level 31) : List_scope.

Inductive Sorted: List -> Prop :=
  | Sorted_empty : Sorted nil
    (* prázdný List je vždy seřazen *)
  | Sorted_one (n : nat) : Sorted (cons n nil)
    (* List s jedním prvkem je také vždy seřazen *)
  | Sorted_cons (n : nat) (m : nat) (rest : List)
    (* List s více prvky [n, m, ...rest] je seřazen, když:*)
      (* 1. n a m jsou správně seřazeny: *)
        (first_pair_sorted : n <= m)
      (* 2. zbytek [m, ...rest] je seřazen: *)
        (rest_sorted : Sorted (cons m rest))
      : Sorted (cons n (cons m rest)).

Theorem Sorted_tail {l a}: Sorted (cons a l) -> Sorted l.
Proof.
  intros.
  inversion H.
  - constructor.
  - apply rest_sorted.
Defined.


Theorem Sorted_append {l1 n l2 m} :
  Sorted (push n l1) ->
  Sorted (cons m l2) ->
  n <= m
  -> Sorted (append (push n l1) (cons m l2)).
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
Defined.

Inductive Elem (n: nat) : List -> Prop :=
  | Elem_triv : forall l, Elem n (n +> l)
  | Elem_cons : forall l u, Elem n l -> Elem n (u +> l).

Notation "a ∈ b" := (Elem a b) (at level 70, no associativity) : List_scope.

Check 5 ∈ [2; 5; 6].

Goal 5 ∈ [2; 5; 6].
  auto using Elem.
  Show Proof.
Defined.


Theorem Elem_tail {l n u}: n ∈ (u +> l) -> n <> u -> n ∈ l.
Proof.
  intros.
  inversion H; subst.
  - contradiction.
  - assumption.
Defined.

Theorem Elem_push l n: Elem n (push n l).
Proof.
  induction l.
  - constructor.
  - simpl.
    constructor.
    exact IHl.
Defined.

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
Defined.

Theorem append_nil l : l ++ [] = l.
Proof.
  induction l.
  - easy.
  - simpl.
    rewrite IHl.
    easy.
Defined.

Theorem Sorted_append0 {l1 l2}  :
  Sorted (l1) ->
  Sorted (l2) ->
  (forall n m, n ∈ l1 -> m ∈ l2 -> n <= m)
  -> Sorted (append l1 l2).
Proof.
  intros.
  destruct l2.
  - rewrite append_nil.
    easy.
  - destruct (List_push_case l1) as [-> | (m & r & ->)].
    + simpl.
      easy.
    + apply Sorted_append; try easy.
      apply H1.
      apply Elem_push.
      apply Elem_triv.
Defined.

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
Defined.

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
Defined.

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
Defined.

Theorem filter_length f l: length (filter f l) <= length l.
  induction l.
  - simpl.
    lia.
  - simpl.
    destruct (f n).
    + simpl.
      lia.
    + lia.
Defined.

Definition Permutation a b : Prop := forall n, count n a = count n b.

Theorem Permutation_symm {l r}: Permutation l r -> Permutation r l.
Proof.
  unfold Permutation.
  intros P n.
  rewrite P.
  reflexivity.
Defined.

Theorem Permutation_Elem0 {l l'}: Permutation l l' -> forall n, Elem n l -> Elem n l'.
Proof.
  intros.
  unfold Permutation in H.
  rewrite <- count_elem in *.
  specialize (H n).
  rewrite <- H.
  exact H0.
Defined.

Theorem Permutation_Elem {l l'}: Permutation l l' -> forall n, Elem n l <-> Elem n l'.
Proof.
  intros.
  split.
  apply Permutation_Elem0.
  assumption.
  apply Permutation_Elem0.
  apply Permutation_symm.
  assumption.
Defined.

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
    rewrite Nat.add_comm.
    symmetry.
    rewrite Nat.add_comm.
    rewrite <- Nat.add_assoc.
    rewrite Nat.add_comm.
    f_equal.
    destruct IHbefore, IHafter.
    induction r.
    + simpl. reflexivity.
    + subst less more before after.
      simpl in *.
      rewrite Nat.leb_antisym.
      destruct (n0 <? p) eqn:E.
      * simpl. lia.
      * simpl. lia.
Defined.

Theorem fquicksort_sorted l: Sorted (fquicksort l).
Proof.
  functional induction (fquicksort l) as [ | ? p l ? IHbefore IHafter].
  - constructor.
  - set (less := fun a => a <? p) in *.
    set (before := filter less l) in *.
    set (more := fun a => p <=? a) in *.
    set (after := filter more l) in *.

    assert ( Sorted (cons p (fquicksort after))) as p_after_sorted. {
      clear IHbefore less before.
      destruct (fquicksort after) as [ | an arest ] eqn:E.
      + constructor.
      + constructor.
        rewrite <- E in *.
        assert (Elem an (an +> arest)) by constructor.
        rewrite <- E in H.
        pose proof (fquicksort_permutation after).
        pose proof (Permutation_Elem H0 an).
        rewrite <- H1 in H.
        clear H0 H1 arest E.
        apply filter_forall in H.
        destruct H as [_ H].
        subst more after.
        simpl in H.
        lia.
        exact IHafter.
    }

    destruct (List_push_case (fquicksort before)) as [-> | H].
    + simpl.
      exact p_after_sorted.
    + destruct H as (n & r & E).
      rewrite E.
      apply Sorted_append.
      * rewrite <- E.
        exact IHbefore.
      * exact p_after_sorted.
      * clear p_after_sorted more after IHafter.
        pose proof (Elem_push r n).
        rewrite <- E in H.
        pose proof (fquicksort_permutation before).
        pose proof (Permutation_Elem H0 n).
        apply H1 in H.
        clear E H0 H1 r.
        subst before less.
        apply filter_forall in H.
        destruct H as [_ H].
        lia.
Defined.


Definition fquicksort_spec: forall l, Permutation l (fquicksort l) /\ Sorted (fquicksort l) :=
  fun l => conj (fquicksort_permutation l) (fquicksort_sorted l).

Fixpoint insert (n : nat) (l : List) : List :=
  match l with
  | [] => [n]
  | m +> r => if n <? m then n +> l else m +> insert n r
  end.

Fixpoint insert_list (i : List) (o : List) : List :=
  match i with
  | [] => o
  | m +> r => insert_list r (insert m o)
  end.

Definition insertsort (l : List) : List := insert_list l [].

Compute insertsort [4;2;7;3;6;4;5;1;8;3;4;6;78;4;3;4;5;45].


Theorem insert_sorted n l: Sorted l -> Sorted (insert n l).
Proof.
  intros.
  induction l.
  simpl. constructor.
  simpl.
  destruct (Nat.ltb_spec n n0).
  constructor.
  lia.
  exact H.
  destruct l.
  simpl. constructor. lia. constructor.
  inversion H; subst.
  specialize (IHl rest_sorted).
  simpl in *.
  destruct (Nat.ltb_spec n n1).
  repeat constructor; try lia. easy.
  constructor.
  lia.
  exact IHl.
Defined.

Theorem insert_list_sorted i o: Sorted o -> Sorted (insert_list i o).
Proof.
  intros.
  generalize dependent o.
  induction i; intros.
  simpl.
  exact H.
  simpl.
  apply IHi.
  exact (insert_sorted n o H).
Defined.

Theorem insertsort_sorted l: Sorted (insertsort l).
Proof.
  unfold insertsort.
  apply insert_list_sorted.
  constructor.
Defined.

Theorem insert_permutation n l: Permutation (n +> l) (insert n l).
Proof.
  unfold Permutation.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  destruct (n <? n1).
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHl; clear IHl.
  simpl.
  repeat rewrite Nat.add_assoc.
  enough (H: forall a b c, a + b + c = b + a + c) by apply H.
  intros.
  rewrite (Nat.add_comm a b).
  reflexivity.
  Show Proof.
Defined.

Theorem insert_list_permutation i o: Permutation (i ++ o) (insert_list i o).
Proof.
  intros n.
  rewrite count_append.
  revert o.
  induction i; intros.
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHi.
  rewrite <- insert_permutation.
  simpl.
  lia.
Defined.

Theorem insertsort_permutation l: Permutation l (insertsort l).
Proof.
  intro n.
  unfold insertsort.
  rewrite <- insert_list_permutation.
  rewrite count_append.
  simpl.
  lia.
Defined.

Definition insertsort_spec l: Sorted (insertsort l) /\ Permutation l (insertsort l)
    := conj (insertsort_sorted l) (insertsort_permutation l).

Compute (insertsort_spec []).

(* Require Import Extraction. *)

(* Extraction Language OCaml. *)
(* Separate Extraction fquicksort insertsort. *)
