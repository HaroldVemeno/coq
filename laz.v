Require Import Basics PeanoNat Bool.
Require Import Lia ZifyBool.

Inductive List : Set :=
  | nil : List
  | cons (n : nat) (tail : List) : List.

Definition Empty (l : List) : Prop := match l with
  | nil => True
  | cons _ _ => False
  end.

Fixpoint length (l : List) : nat := match l with
  | nil => 0
  | cons _ rest => 1 + length rest
  end.

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

Fixpoint elem (n:nat) (l:List) : bool := match l with
  | nil => false
  | cons m r => (if n =? m then true else elem n r)
end.

Inductive Elem (n: nat) : List -> Prop :=
  | Elem_triv : forall l, Elem n (cons n l)
  | Elem_cons : forall l u, Elem n l -> Elem n (cons u l).

Theorem Elem_tail {l n u}: Elem n (cons u l) -> n <> u -> Elem n l.
Proof.
  intros.
  inversion H.
  - contradiction.
  - assumption.
Qed.

Theorem Elem_el0 {l n u} : Elem n (cons u l) <-> n = u \/ (Elem n l /\ n <> u).
Proof.
  intros.
  split.
  - destruct (Nat.eq_decidable n u).
    left. exact H.
    right.
    split.
    + apply (Elem_tail H0 H).
    + assumption.
  - intros.
    destruct H as [-> | E].
    + apply Elem_triv.
    + apply Elem_cons.
      destruct E.
      exact H.
      Show Proof.
Qed.


Theorem Elem_el {l n u} : Elem n (cons u l) <-> n = u \/ Elem n l.
Proof.
  intros.
  split.
  - destruct (Nat.eq_decidable n u).
    left. exact H.
    right.
    apply (Elem_tail H0 H).
  - intros.
    destruct H as [-> | E].
    + apply Elem_triv.
    + apply Elem_cons.
      exact E.
Qed.

Theorem elem_spec n l: Elem n l <-> elem n l = true.
Proof.
  split.
  - intro E.
    induction l.
    + inversion E.
    + simpl.
      destruct (Nat.eqb_spec n n0); [reflexivity| ].
      apply IHl.
      apply Elem_el in E.
      destruct E; [contradiction | ].
      exact H.
  - intro E.
    induction l.
    + simpl in E.
      discriminate E.
    + simpl in E.
      destruct (Nat.eqb_spec n n0) as [-> | D].
      * apply Elem_triv.
      * apply Elem_cons.
        exact (IHl E).
Qed.

Definition elem_reflect n l: reflect (Elem n l) (elem n l) := iff_reflect _ _ (elem_spec n l).

Theorem elem_not_nil : forall l n, Elem n l -> l <> nil.
Proof.
  intros.
  destruct l.
  - inversion H.
  - discriminate.
Qed.

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

Fixpoint append (a b : List) : List :=
  match a with
    | nil => b
    | cons ah ar => cons ah (append ar b)
  end.

Fixpoint lastd (n : nat) (l : List) : nat :=
  match l with
  | nil => n
  | cons m r => lastd m r
  end.

Definition last (l : List) : if l then unit else nat :=
  match l with
  | nil => tt
  | cons m r => lastd m r
  end.

Definition head (l : List) : if l then unit else nat :=
  match l with
  | nil => tt
  | cons m r => m
  end.

Declare Scope List_scope.
Delimit Scope List_scope with List.
Open Scope List_scope.

Notation "a +> b" := (cons a b) (right associativity, at level 100) : List_scope.
Notation "[ ]" := nil : List_scope.
Notation "[ a ; .. ; e ]" := ( cons a .. (cons e nil) ..) : List_scope.
Notation "a ++ b" := (append a b) : List_scope.
Notation "a <+ b" := (push b a) (left associativity, at level 101) : List_scope.


Theorem append_nil {a}: append a nil = a.
Proof.
  induction a.
  - reflexivity.
  - simpl.
    rewrite IHa.
    reflexivity.
Qed.

Theorem append_comm {a b c}: append a (append b c) = append (append a b) c.
Proof.
  induction a.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHa.
    reflexivity.
Qed.

Theorem append_length a b: length (append a b) = length a + length b.
Proof.
  induction a.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHa.
    reflexivity.
Qed.

Theorem Elem_push l n: Elem n (push n l).
Proof.
  induction l.
  - constructor.
  - simpl.
    constructor.
    exact IHl.
Qed.

Theorem append_push l a: append l (cons a nil) = push a l.
Proof.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Qed.

Theorem cons_push_comm l a b: cons a (push b l) = push b (cons a l).
Proof.
  simpl.
  reflexivity.
Qed.


Theorem reverse_cons l a: reverse (cons a l) = push a (reverse l).
Proof.
  simpl.
  reflexivity.
Qed.

Theorem reverse_push l a: reverse (push a l) = cons a (reverse l).
Proof.
  induction l.
  - reflexivity.
  - simpl.
    rewrite IHl.
    simpl.
    reflexivity.
Qed.

Theorem reverse_reverse l: reverse (reverse l) = l.
Proof.
  induction l.
  - reflexivity.
  - simpl.
    rewrite reverse_push.
    rewrite IHl.
    reflexivity.
Qed.

Theorem reverse_exists l: exists rl, l = reverse rl.
Proof.
  induction l.
  - exists nil.
    reflexivity.
  - destruct IHl.
    rewrite H.
    exists (push n x).
    rewrite reverse_push.
    reflexivity.
Qed.

Theorem List_push_ind: forall (P: List -> Prop), P nil -> (forall n tail, P tail -> P (push n tail)) -> forall l, P l.
Proof.
  intros.
  destruct (reverse_exists l).
  rewrite H1.
  clear H1 l.
  induction x.
  - simpl.
    exact H.
  - simpl.
    apply H0.
    exact IHx.
Qed.

Theorem List_push_case l: l = nil \/ exists n r, l = push n r.
Proof.
  intros.
  induction l using List_push_ind.
  - left. reflexivity.
  - right.
    exists  n.
    exists l.
    reflexivity.
Qed.

Theorem push_length l a: length (push a l) = S (length l).
Proof.
  induction l.
  - reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Qed.

Theorem push_nnil l a: nil <> push a l.
Proof.
  induction l; discriminate.
Qed.

Theorem Sorted_tail {l a R}: Sorted R (cons a l) -> Sorted R l.
Proof.
  intros.
  inversion H.
  - constructor.
  - apply rest_sorted.
Qed.

Theorem Sorted_pop {l a R}: Sorted R (push a l) -> Sorted R l.
Proof.
  intros.
  destruct l.
    apply Sorted_empty.
  generalize dependent a.
  generalize dependent n.
  induction l; intros.
    apply Sorted_one.
  simpl in H.
  inversion H; subst.
  simpl in rest_sorted.
  apply IHl in rest_sorted.
  apply Sorted_cons.
  - exact first_pair_sorted.
  - exact rest_sorted.
Qed.

Theorem Sorted_app1 {a b R}:
  Sorted R (append a b)
  -> Sorted R a.
Proof.
  intros.
  destruct a.
    constructor.
  generalize dependent n.
  induction a; intros.
    constructor.
  simpl in *.
  inversion H.
  subst.
  constructor.
  assumption.
  exact (IHa n rest_sorted).
Qed.

Theorem Sorted_app2 {a b R}:
  Sorted R (append a b)
  -> Sorted R b.
Proof.
  intros.
  destruct a.
    destruct b.
    constructor.
    simpl in H.
    assumption.
  generalize dependent n.
  induction a; intros.
    destruct b.
    constructor.
    simpl in H.
    exact (Sorted_tail H).
  simpl in *.
  exact (IHa n (Sorted_tail H)).
Qed.


Theorem Sorted_push {l a b R}:
  Sorted R (push a l) ->
  R a b
  -> Sorted R (push b (push a l)).
Proof.
  intros.
  induction l.
  - simpl in *.
    apply Sorted_cons.
    exact H0.
    apply Sorted_one.
  - simpl in *.
    pose proof (Sorted_tail H).
    apply IHl in H1.
    destruct l.
      simpl in *.
      inversion H; subst.
      auto using Sorted.
    simpl in *.
    inversion H; subst.
    constructor.
    exact first_pair_sorted.
    exact H1.
Qed.

Theorem Sorted_reverse l R: Sorted R l -> Sorted (flip R) (reverse l).
Proof.
  intros S.
  destruct l.
    constructor.
  generalize dependent n.
  induction l; intros.
    constructor.
  simpl in *.
  apply Sorted_push.
  apply Sorted_tail in S.
  apply IHl.
  exact S.
  unfold flip.
  inversion S; subst.
  exact first_pair_sorted.
Qed.

Theorem Sorted_unreverse l R: Sorted R (reverse l) -> Sorted (flip R) l.
Proof.
  intros S.
  destruct (reverse_exists l).
  subst.
  rewrite reverse_reverse in S.
  apply Sorted_reverse.
  exact S.
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

Fixpoint min (n: nat) (l: List): nat :=
  match l with
    | nil => n
    | cons m t => if m <? n then min m t else min n t
  end.

Theorem min_elem {n l}: Elem (min n l) (cons n l).
Proof.
  generalize dependent n.
  induction l; intros.
  - simpl.
    constructor.
  - simpl in *.
    destruct (Nat.ltb_spec n n0).
    constructor.
    apply IHl.
    specialize (IHl n0).
    rewrite Elem_el in IHl.
    rewrite Elem_el.
    destruct IHl.
    rewrite H0.
    left. reflexivity.
    right.
    constructor.
    exact H0.
Qed.

Theorem min_refl n l: min n l <= n.
Proof.
  generalize dependent n.
  induction l; intros.
  - simpl. lia.
  - simpl.
    destruct (Nat.ltb_spec n n0).
    + specialize (IHl n).
      lia.
    + apply IHl.
Qed.

Theorem min_inj n m l: n <= m -> min n l <= min m l.
Proof.
  intros.
  generalize dependent m.
  generalize dependent n.
  induction l; intros.
  - simpl.
    lia.
  - simpl.
    destruct (Nat.ltb_spec n n0), (Nat.ltb_spec n m).
    + lia.
    + lia.
    + specialize (IHl n0 n H0).
      lia.
    + specialize (IHl n0 m H).
      lia.
Qed.

Theorem min_lt_elem {n l x}: Elem x l ->  min n l <= x.
Proof.
  intros.
  induction l.
  - inversion H.
  - apply Elem_el in H.
    destruct H.
    subst.
    simpl.
    destruct (Nat.ltb_spec n0 n).
    apply min_refl.
    pose proof (min_refl n l).
    lia.
    specialize (IHl H).
    simpl.
    destruct (Nat.ltb_spec n0 n).
    assert (n0 <= n) by lia.
    pose proof (min_inj n0 n l H1).
    lia.
    lia.
Qed.

Notation LeSorted := (Sorted le).

Theorem LeSorted_min {l} n : LeSorted l -> LeSorted (cons (min n l) l).
Proof.
  intros.
  generalize dependent n.
  induction l; intros.
    simpl.
    constructor.
  simpl.
  destruct (Nat.ltb_spec n n0).
  - constructor.
    + apply min_refl.
    + exact H.
  - constructor.
    + pose proof (min_refl n0 l).
      lia.
    + exact H.
Qed.

Fixpoint remove_elem n l: List :=
  match l with
    | nil => nil
    | cons m l' => if m =? n then remove_elem n l' else cons m (remove_elem n l')
  end.

Theorem List_strong_ind:
  forall P : (List -> Prop),
  P nil ->
  (forall l, (forall r, length r < length l -> P r) -> P l)
  -> forall l, P l.
Proof.
  intros.
  assert (exists r, length l < length r).
    exists (cons 8 l).
    simpl.
    lia.
  destruct H1.
  generalize dependent l.
  induction x; intros.
  - simpl in H1.
    lia.
  - simpl in H1.
    assert (length l <= length x) by lia.
    Nat.le_elim H2.
    + apply IHx.
      exact H2.
    + apply H0.
      intros.
      apply IHx.
      lia.
Qed.

Theorem List_strong_ind0:
  forall P : (List -> Prop),
  P nil ->
  (forall l, (forall r, length r <= length l -> P r) -> forall n, P (cons n l) )
  -> forall l, P l.
Proof.
  intros.
  destruct l.
  exact H.
  assert (exists r, length (cons n l) <= length r).
    exists (cons 9 l).
    simpl.
    lia.
  destruct H1.
  generalize dependent l.
  generalize dependent n.
  induction x; intros.
  - simpl in H1.
    lia.
  - simpl in H1.
    assert (length l <= length x) by lia.
    Nat.le_elim H2.
    + apply IHx.
      exact H2.
    + apply H0.
      intros.
      destruct r.
      exact H.
      apply IHx.
      lia.
Qed.

Theorem Sorted_over {n m l}: LeSorted (cons n (cons m l)) -> LeSorted (cons n l).
Proof.
  intros.
  destruct l.
  constructor.
  inversion H. subst.
  inversion rest_sorted. subst.
  constructor.
  lia.
  assumption.
Qed.

Theorem Sorted_remove_elem {l} n: LeSorted l -> LeSorted (remove_elem n l).
Proof.
  intros.
  destruct l.
    simpl.
    constructor.
  generalize dependent n0.
  generalize dependent n.
  induction l; intros.
  - simpl.
    destruct (n0 =? n); constructor.
  - simpl.
    destruct (Nat.eqb_spec n1 n0);
    destruct (Nat.eqb_spec n n0); subst.
    + apply Sorted_tail in H.
      specialize (IHl n0 0).
      assert (LeSorted (cons 0 l)). {
        destruct l.
        * constructor.
        * apply Sorted_cons.
          lia.
          exact (Sorted_tail H).
      }
      specialize (IHl H0).
      simpl in IHl.
      destruct n0.
      * exact IHl.
      * exact (Sorted_tail IHl).
    + simpl in *.
      assert (n =? n0 = false) by lia.
      specialize (IHl n0 n (Sorted_tail H)).
      rewrite H0 in IHl.
      exact IHl.
    + simpl in *.
      assert (n1 =? n0 = false) by lia.
      specialize (IHl n0 n1 (Sorted_over H)).
      rewrite H0 in IHl.
      exact IHl.
    + simpl in *.
      assert (n =? n0 = false) by lia.
      specialize (IHl n0 n (Sorted_tail H)).
      rewrite H0 in IHl.
      inversion H. subst.
      constructor.
      * exact first_pair_sorted.
      * exact IHl.
Qed.

Fixpoint count (n : nat) (l : List) : nat :=
  match l with
    | nil => 0
    | cons m lr => (if m =? n then 1 else 0) + count n lr
  end.

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
      rewrite Elem_el0 in H.
      destruct H.
      * subst.
        rewrite Nat.eqb_refl.
        lia.
      * simpl.
        destruct H.
        assert (n0 =? n = false) by lia.
        rewrite H1.
        simpl.
        apply (IHl H).
Qed.

Definition Permutation a b : Prop := forall n, count n a = count n b.

Goal Permutation (cons 4 (cons 6 nil)) (cons 6 (cons 4 nil)).
Proof.
  unfold Permutation.
  intros.
  do 6 try destruct n.
  all: simpl.
  all: reflexivity.
Qed.

Theorem Permutation_refl l : Permutation l l.
Proof.
  intro.
  reflexivity.
Qed.

Theorem Permutation_symm {a b} : Permutation a b -> Permutation b a.
Proof.
  intros H n.
  specialize (H n).
  rewrite H.
  reflexivity.
Qed.

Theorem Permutation_trans {a b c} : Permutation a b -> Permutation b c -> Permutation a c.
Proof.
  unfold Permutation.
  intros AB BC n.
  rewrite AB.
  apply BC.
Qed.

Theorem count_append a b : forall n, count n (append a b) = count n a + count n b.
Proof.
  generalize dependent b.
  induction a; intros.
  - simpl.
    reflexivity.
  - simpl.
    destruct (Nat.eqb_spec n n0).
    + subst.
      simpl.
      f_equal.
      apply IHa.
    + simpl.
      apply IHa.
Qed.


Theorem count_push a m: forall n, count n (push m a) = count n (cons m a).
Proof.
  intro.
  rewrite <- append_push.
  rewrite count_append.
  simpl.
  lia.
Qed.

Theorem Permutation_reverse l: Permutation l (reverse l).
Proof.
  intro.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite count_push.
    simpl.
    rewrite IHl.
    reflexivity.
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
  split. {
    generalize dependent n.
    induction l.
    - intros.
      simpl in H.
      inversion H.
    - intros.
      simpl in H.
      destruct (f n).
      + rewrite Elem_el0 in H.
        destruct H as [].
        * subst.
          constructor.
        * constructor.
          apply IHl.
          apply H.
      + constructor.
        apply IHl.
        exact H.
  } {
    generalize dependent n.
    induction l.
    - intros.
      simpl in H.
      inversion H.
    - intros.
      simpl in H.
      destruct (f n) eqn:E.
      + destruct (Nat.eqb_spec n0 n).
        * subst.
          exact E.
        * apply IHl.
          apply Elem_tail in H.
          exact H. exact n1.
      + apply IHl.
        exact H.
  }
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

Theorem filter_comp f g l: filter f (filter g l) = filter (fun x => f x && g x) l.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    all: destruct (g n).
    all: simpl.
    all: destruct (f n).
    all: simpl.
    all: rewrite IHl.
    all: reflexivity.
Qed.

Eval compute in filter (fun a => a <? 8) (cons 2 (cons 6 (cons 8 (cons 11 (cons 3 nil))))).

Fixpoint qs (u : nat) (l : List) : List :=
  match l, u with
  | cons p r, S v => append (qs v (filter (fun a => a <? p) r))
              (cons p (qs v (filter (fun a => p <=? a) r)))
  | _, _ => nil
  end.

Definition quicksort (l: List) : List := qs (length l) l.

Eval compute in quicksort (cons 2 (cons 6 (cons 8 (cons 11 (cons 3 nil))))).
Eval compute in quicksort nil.

Theorem le_to_add {n m}: n <= m -> exists x, x + n = m.
Proof .
  intros.
  induction n.
  - exists m.
    lia.
  - destruct m.
    + lia.
    + assert (n <= S m) by lia.
      specialize (IHn H0).
      destruct IHn.
      destruct x; simpl in *.
      * lia.
      * exists x.
        lia.
Qed.

Theorem qs_u_irrelevant0 {l} u: qs (length l) l = qs (u + length l) l.
Proof.
  replace (length l) with (0 + length l) by lia.
  generalize 0 as v.
  revert u.
  induction l using List_strong_ind0; intros.
  - simpl.
    destruct u.
    + simpl. reflexivity.
    + simpl. destruct v; reflexivity.
  - simpl.
    replace (v + S (length l)) with (S (v + length l)) by lia.
    replace (u + S (v + length l)) with (S (u + v + length l)) by lia.
    simpl.
    f_equal.
    + remember (fun a => a <? n) as less.
      pose proof (filter_length less l).
      remember (filter less l) as before.
      pose proof (H _ H0).
      destruct (le_to_add H0).
      specialize (H1 u (v + x)).
      rewrite <- H2.
      repeat rewrite Nat.add_assoc in *.
      exact H1.
    + remember (fun a => n <=? a) as more.
      pose proof (filter_length more l).
      remember (filter more l) as after.
      f_equal.
      pose proof (H _ H0).
      destruct (le_to_add H0).
      specialize (H1 u (v + x)).
      rewrite <- H2.
      repeat rewrite Nat.add_assoc in *.
      exact H1.
Qed.

Theorem qs_u_irrelevant {l u}: length l <= u -> qs (length l) l = qs u l.
Proof.
  intros.
  destruct (le_to_add H) as [? <-].
  apply qs_u_irrelevant0.
Qed.

Theorem Elem_case l: l = nil \/ exists n, Elem n l.
Proof.
  destruct l.
  - left.
    reflexivity.
  - right.
    exists n.
    constructor.
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

Theorem quicksort_permutation l: Permutation l (quicksort l).
Proof.
  unfold quicksort.
  induction l as [| l IH p] using List_strong_ind0 .
  - simpl.
    intros n.
    simpl.
    reflexivity.
  - intros n.
    simpl.
    rewrite count_append.
    simpl.

    remember (fun a => a <? p) as less.
    pose proof (filter_length less l).
    remember (filter less l) as before.
    pose proof (IH _ H).
    rewrite (qs_u_irrelevant H) in H0.
    specialize (H0 n).
    rewrite <- H0.
    clear H0 H.

    remember (fun a => p <=? a) as more.
    pose proof (filter_length more l).
    remember (filter more l) as after.
    pose proof (IH _ H).
    rewrite (qs_u_irrelevant H) in H0.
    specialize (H0 n).
    rewrite <- H0.
    clear H0 H.

    enough (count n l = count n before + count n after) by lia.
    clear IH.
    subst.
    induction l.
    + subst.
      simpl.
      reflexivity.
    + simpl.
      destruct (Nat.ltb_spec n0 p).
      * replace (p <=? n0) with false by lia.
        simpl.
        lia.
      * replace (p <=? n0) with true by lia.
        simpl.
        lia.
Qed.

Theorem quicksort_sorted l: LeSorted (quicksort l).
Proof.
  unfold quicksort.
  induction l as [| l IH p] using List_strong_ind0 .
  - compute.
    constructor.
  - simpl.
    remember (fun a => a <? p) as less.
    pose proof (filter_length less l).
    remember (filter less l) as before.
    remember (fun a => p <=? a) as more.
    pose proof (filter_length more l).
    remember (filter more l) as after.
    pose proof (IH _ H).
    rewrite (qs_u_irrelevant H) in H1.
    pose proof (IH _ H0).
    rewrite (qs_u_irrelevant H0) in H2.
    assert (LeSorted (cons p (qs (length l) after))). {
      clear IH H H1 Heqless Heqbefore less before.
      pose proof (quicksort_permutation after).
      unfold quicksort in *.
      rewrite (qs_u_irrelevant H0) in H.
      pose proof (filter_forall l more).
      rewrite <- Heqafter in H1.
      remember (qs (length l) after) as qafter.
      destruct qafter.
      constructor.
      specialize (H1 n).
      pose proof (Permutation_Elem (Permutation_symm H) n).
      assert (Elem n (cons n qafter)) by constructor.
      specialize (H3 H4).
      destruct (H1 H3).
      subst more.
      constructor.
      lia.
      exact H2.
    }
    destruct (List_push_case (qs (length l) before)).
    + rewrite H4.
      simpl.
      exact H3.
    + destruct H4 as (n & r & H4).
      rewrite H4.
      apply Sorted_append.
      rewrite <- H4.
      exact H1.
      exact H3.
      clear IH H1 H2 H3 H0 Heqmore more Heqafter after.
      pose proof (quicksort_permutation before).
      unfold quicksort in *.
      rewrite (qs_u_irrelevant H) in H0.
      pose proof (Elem_push r n).
      rewrite <- H4 in H1.
      pose proof (filter_forall l less).
      rewrite <- Heqbefore in H2.
      pose proof (Permutation_Elem (Permutation_symm H0) n).
      specialize (H3 H1).
      destruct (H2 n H3).
      subst less.
      lia.
Qed.

Require Import FunInd Recdef.

Function fquicksort (l : List) {measure length l} : List :=
  match l with
  | nil => nil
  | cons p r => append (fquicksort (filter (fun a => a <? p) r))
              (cons p (fquicksort (filter (fun a => p <=? a) r)))
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

Search "fquicksort".

Print fquicksort.
Print fquicksort_terminate.

Eval vm_compute in fquicksort (cons 2 (cons 6 (cons 8 (cons 11 (cons 3 nil))))).

Eval vm_compute in (6 +> 5 +> []).

Eval vm_compute in fquicksort  (6 +> 7 +> 1 +> 0 +> 100 +> 2 +> 20 +> 120 +> 130 +> 140 +> 151 +> 156 +> nil).

Eval vm_compute in fquicksort [6; 7; 1; 0; 100; 2; 20; 120; 130; 140; 151; 156].

Eval vm_compute in (5 +> 1 +> nil <+ 6 <+ 19).

Eval vm_compute in fquicksort [6; 5; 4; 3; 7; 5; 7; 2; 7; 1; 7; 8; 2; 5; 7; 3; 9].

Eval vm_compute in filter (fun a => 0 <? a) [ 6 ; 7 ; 1 ; 0 ; 100 ; 2 ; 20 ; 120 ; 130 ; 140 ; 151 ; 156].

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
