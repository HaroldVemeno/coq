Require Import Nat PeanoNat Bool BoolEq EqNat Le Orders.
Require Import Lia ZifyBool.

Open Scope nat_scope.

Theorem refl : forall a : nat, a = a.
Proof.
  intro.
  reflexivity.
Qed.

Locate Nat.
Locate beq_nat.

Definition refl_example : S (S (S O)) = 3 := eq_refl 3.

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

Fixpoint sum (l : List) : nat := match l with
  | nil => 0
  | cons n rest => n + sum rest
  end.

Theorem sum_example : sum (cons 5 (cons 4 (cons 8 nil))) = 17.
Proof.
  cbv delta; fold Nat.add; cbv iota; fold sum.
  cbv beta.
  cbv iota.
  cbv.
  reflexivity.
Qed.

Inductive Sorted: List -> Prop :=
  | Sorted_empty : Sorted nil
    (* prázdný List je vždy seřazen *)
  | Sorted_one (n : nat) : Sorted(cons n nil)
    (* List s jedním prvkem je také vždy seřazen *)
  | Sorted_recursive (n : nat) (m : nat) (rest : List)
    (* List s více prvky [n, m, ...rest] je seřazen, když:*)
      (* 1. n a m jsou správně seřazeny: *)
        (first_pair_sorted : n <= m) 
      (* 2. zbytek [m, ...rest] je seřazen: *)
        (rest_sorted : Sorted (cons m rest))
      : Sorted (cons n (cons m rest)).

Theorem example_sorted : Sorted (cons 2 (cons 3 (cons 5 nil))).
Proof.
  refine (Sorted_recursive 2 3 (cons 5 nil) _ _).
  auto.
  (* Dokonce lze odvodit úplně vše *)
  (* refine (recursive_sorted _ _ _ _ _). *)
  constructor.
  auto.
  (* Zbytek už je jednoduchý *)
  refine (Sorted_one 5).
Qed.

Theorem example_not_sorted : ~ Sorted (cons 5 (cons 5 (cons 2 nil))).
Proof.
  unfold not.
  intro S.
  inversion S.
  clear n m rest first_pair_sorted H0 H1 H2 S.

  inversion rest_sorted.
  clear n m rest H0 H1 H2 rest_sorted rest_sorted0.


  repeat apply le_S_n in first_pair_sorted.
  apply Nat.nle_succ_0 in first_pair_sorted.
  apply first_pair_sorted.
Qed.

Fixpoint min_elem (l:List) : option nat := match l with
  | nil => None
  | cons n r => Some (match min_elem r with
    | None => n
    | Some m => if n <? m then n else m
  end)
end.


Theorem example_min_elem : min_elem (cons 4 (cons 6 (cons 2 nil))) = Some 2.
Proof.
  compute.
  reflexivity.
Qed.

Theorem has_min : forall (l : List), length l > 0 -> exists (n : nat), min_elem l = Some n.
Proof.
  intros.
  induction l.
  - compute in H.
    apply le_n_0_eq in H.
    discriminate.
  - clear IHl H.
    simpl.
    eauto.
  (* Show Proof. *)
Qed.

Fixpoint elem (n:nat) (l:List) : bool := match l with
  | nil => false
  | cons m r => (if n =? m then true else elem n r)
end.

Inductive Elem (n: nat) : List -> Prop :=
  | Elem_triv : forall l, Elem n (cons n l)
  | Elem_cons : forall l u, Elem n l -> Elem n (cons u l).

Theorem Elem_tail: forall l n u, Elem n (cons u l) -> n <> u -> Elem n l.
Proof.
  intros.
  inversion H.
  - contradiction.
  - exact H2.
Qed.

Theorem Elem_el: forall l n u, Elem n (cons u l) <-> n = u \/ Elem n l.
Proof.
  intros.
  split.
  - destruct (Nat.eq_decidable n u).
    left. exact H.
    right.
    apply (Elem_tail _ _ _ H0 H).
  - intros.
    destruct H as [-> | E].
    apply Elem_triv.
    apply Elem_cons.
    exact E.
Qed.

Theorem elem_spec n l: Elem n l <-> elem n l = true.
Proof.
  split.
  - intro E.
    induction l.
    + inversion E.
    + simpl.
      Search reflect.
      destruct (Nat.eqb_spec n n0); [reflexivity| ].
      apply IHl.
      apply Elem_el in E.
      destruct E; [contradiction |].
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

Theorem elem_reflect n l: reflect (Elem n l) (elem n l).
  induction l.
  simpl.
  apply ReflectF.
  intro.
  inversion H.
  inversion IHl.
  simpl.
  destruct (Nat.eqb_spec n n0).
  apply ReflectT.
  rewrite e.
  apply Elem_triv.
  rewrite <- H.
  apply ReflectT.
  apply Elem_cons.
  exact H0.
  simpl.
  destruct (Nat.eqb_spec n n0).
  apply ReflectT.
  rewrite e.
  apply Elem_triv.
  rewrite <- H.
  apply ReflectF.
  intro.
  apply Elem_el in H1.
  destruct H1; contradiction.
Qed.

Theorem elem_not_nil : forall l n, Elem n l -> length l > 0. 
Proof.
  intros.
  induction l.
  - compute in H.
    inversion H.
  - compute.
    apply le_n_S.
    apply le_0_n.
Qed.

Fixpoint remove_elem n l: List :=
  match l with
    | nil => nil
    | cons m l' => if m =? n then remove_elem n l' else cons m (remove_elem n l')
  end.

Ltac conv_eq := match goal with
                  | H : (?a =? ?b) = true  |- _ => apply beq_nat_true  in H; conv_eq
                  | H : (?a =? ?b) = false |- _ => apply beq_nat_false in H; conv_eq
                  | _ => idtac
                end.

Ltac conv_ord := conv_eq; match goal with
                  | H : (?a <? ?b) = true  |- _ => apply Nat.ltb_lt    in H; conv_ord
                  | H : (?a <? ?b) = false |- _ => apply Nat.ltb_ge    in H; conv_ord
                  | _ => idtac
                end.

Theorem elem_remove_elem: forall l n m, Elem n l -> n <> m -> Elem n (remove_elem m l).
Proof.
  intros.
  induction l.
  compute.
  exact H.
  simpl.
  destruct (n0 =? m) eqn:E.
  - conv_eq.
    destruct E.
    pose proof (Elem_tail _ _ _ H H0).
    exact (IHl H1).
  -
    destruct (Nat.eq_decidable n0 n).
    + destruct H1.
      apply Elem_triv.
    + apply Elem_cons.
      apply Elem_tail in H; [ |apply not_eq_sym; exact H1].
      apply IHl.
      exact H.
Qed.


Theorem len_gt_0_cons : forall l, length l > 0 -> exists n i, l = cons n i.
Proof.
  intros.
  induction l.
  compute in H.
  apply Nat.nle_succ_0 in H.
  contradiction.
  eauto.
Qed.

Theorem len_gt_0_not_nil : forall l, length l > 0 <-> l <> nil.
Proof.
  split.
  intros.
  induction l.
  compute in H.
  apply Nat.nle_succ_0 in H.
  contradiction.
  discriminate.
  intros.
  induction l.
  contradiction.
  simpl.
  compute.
  apply le_n_S.
  apply le_0_n.
Qed.

Theorem min_elem_cons : forall l n, min_elem (cons n l) <> None.
Proof.
  intros.
  simpl.
  discriminate.
Qed.

Theorem total : forall l, length l > 0 -> min_elem l <> None.
Proof.
  intros.
  apply len_gt_0_cons in H.
  destruct H as [n [ll e]].
  rewrite e.
  simpl.
  discriminate.
Qed.

Definition min_elem1 (l:List) (D: length l > 0): nat :=
  match min_elem l as min return min <> None -> nat with 
    | Some a => fun _ => a
    | None => fun E => match E eq_refl with end
  end (total l D).

Definition min_elem1_alt (l:List) (D: length l > 0): nat.
  refine (match min_elem l as min return min <> None -> nat with 
    | Some a => fun _ => a
    | None => fun E => _
  end (total l D)).
  destruct E.
  reflexivity.
  (* Show Proof. *)
Defined.

Definition min_elem1_alt2 (l:List) (D: length l > 0): nat.
  destruct (min_elem l) eqn:E.
  - exact n.
  - pose proof (total l D).
    contradiction (H E).
Defined.

Definition min_elem1_alt3 (l:List) (D: length l > 0): nat :=
  match min_elem l as min return min <> None -> nat with 
    | Some a => fun _ => a
    | None => fun E => ltac:(contradiction)
  end (total l D).

Definition min_elem1_alt4 (l:List) (D: length l > 0): nat :=
  match min_elem l as min return min <> None -> nat with 
    | Some a => fun _ => a
    | None => fun E: None <> None => ltac:(contradiction) 
  end (total l D).

Print min_elem1_alt.
Print min_elem1_alt2.
Print min_elem1_alt3.
Print min_elem1_alt4.
(* Search beq_nat. *)

Theorem min_spec_elem: forall l H, Elem (min_elem1 l H) l.
Proof.
  intro.
  destruct l.
  - intros L.
    pose proof (Nat.nle_succ_0 _ L).
    contradiction H.
  - induction l; intros.
    + unfold min_elem1.
      simpl.
      apply Elem_triv.
    + assert (length (cons n l) > 0) by (simpl; lia).
      pose proof (IHl H0).
      clear IHl.
      unfold min_elem1 in *.
      simpl in *.
      destruct (min_elem l).
      destruct (n <? n1) eqn:E1;
      destruct (n0 <? n1) eqn:E2;
      destruct (n <? n0) eqn:E3;
      try rewrite E1.
      apply Elem_triv.
      apply Elem_cons. apply Elem_triv.
      apply Elem_triv.
      apply Elem_triv.
      apply Elem_triv.
      apply Elem_cons. apply Elem_triv.
      destruct (Nat.eq_dec n n1).
      rewrite e.
      apply Elem_triv.
      assert (n1 <> n) by auto.
      pose proof (Elem_tail _ _ _ H1 H2).
      apply Elem_cons.
      apply Elem_cons.
      exact H3.
      destruct (Nat.eq_dec n n1).
      rewrite e.
      apply Elem_triv.
      assert (n1 <> n) by auto.
      pose proof (Elem_tail _ _ _ H1 H2).
      apply Elem_cons.
      apply Elem_cons.
      exact H3.
      destruct (n <? n0) eqn:E3.
      apply Elem_triv.
      apply Elem_cons. apply Elem_triv.
Qed.

Theorem min_spec_min: forall (l:List) (n:nat) (E : Elem n l),
  let E1 := elem_not_nil l n E in min_elem1 l E1 <= n.
Proof.
  intro l.
  destruct l.
  - intros.
    compute in E.
    inversion E.
  - intros. induction l.
    + compute.
      destruct (n0 =? n) eqn:Eqn.
      * lia.
      * apply beq_nat_false in Eqn.
        pose proof (Elem_tail _ _ _ E Eqn) as H.
        inversion H.
    + unfold min_elem1.
      subst E1.
      simpl.
      destruct (n0 =? n1) eqn:Eqn.
      * apply beq_nat_true in Eqn.
        destruct (min_elem l).
        -- destruct (n1 <? n2) eqn:Eqn1,
                    (n  <? n1) eqn:Eqn2,
                    (n  <? n2) eqn:Eqn3.
           lia. lia. lia. lia. lia. lia. lia. lia.
        -- destruct (n <? n1) eqn:Eqn2.
           lia. lia.
      * rewrite elem_spec in E.
        simpl in E.
        rewrite Eqn in E.
        apply beq_nat_false in Eqn.
        assert ((if n0 =? n then true else elem n0 l) = elem n0 (cons n l)) by auto.
        rewrite H in E.
        rewrite <- elem_spec in E.
        clear H. pose proof (IHl E) as IHL. clear IHl.
        unfold min_elem1 in IHL.
        simpl in IHL.
        destruct (min_elem l).
        -- destruct (n1 <? n2) eqn:Eqn1,
                    (n  <? n1) eqn:Eqn2,
                    (n  <? n2) eqn:Eqn3;
           lia.
        -- destruct (n <? n1) eqn:Eqn2;
           lia.
Qed.


Theorem Min1_spec :
  forall l n (E: Elem n l),
  let D := elem_not_nil l n E in
  Elem (min_elem1 l D) l
  /\ min_elem1 l D <= n.
Proof.
 intros.
 split.
 apply min_spec_elem.
 apply min_spec_min.
Qed.

Fixpoint min_def n l: nat:= match l with
                            | nil => n
                            | cons m l' => let min' := min_def n l' in if min' <? m then min' else m
                          end.

Fixpoint remove_once n l: List := match l with
                                    | nil => nil
                                    | cons m l' => if n =? m then l' else cons m (remove_once n l')
                                  end.

Fixpoint emplace n l: List := match l with
  | nil => cons n nil
  | cons m l' => if m <? n then cons m (emplace n l') else cons n l
end.

Definition insert_sort l: List := (fix ins o i := match i with
      | nil => o
      | cons m l' => ins (emplace m o) l'
end) nil l.

Eval vm_compute in insert_sort (cons 4 (cons 6 (cons 1 (cons 3 (cons 2 nil))))).
Eval vm_compute in insert_sort (cons 5 (cons 4 (cons 3 (cons 2 (cons 1 nil))))).
Eval vm_compute in insert_sort (cons 5 (cons 4 (cons 5 (cons 8 (cons 5 (cons 3 nil)))))).


Theorem Sorted_le: forall a b l, Sorted (cons a (cons b l)) -> a <= b.
  intros.
  inversion H.
  exact first_pair_sorted.
Qed.

Theorem Sorted_tail: forall n l, Sorted (cons n l) -> Sorted l.
  intros.
  inversion H.
  - apply Sorted_empty.
  - exact  rest_sorted.
Qed.

Theorem Sorted_under: forall a b l, Sorted (cons a (cons b l)) -> Sorted (cons a l).
  intros.
  destruct l.
  apply Sorted_one.
  inversion H.
  inversion rest_sorted.
  apply Sorted_recursive.
  lia.
  exact rest_sorted0.
Qed.


Ltac miniinv0 H := try pose proof (Sorted_tail _ _ H) as ?H;
                   try pose proof (Sorted_le _ _ _ H) as ?Le;
                   try pose proof (Sorted_under _ _ _ H) as ?U.

Ltac miniinv H := miniinv0 H.

Theorem Sorted_under2: forall a b c l, Sorted (cons a (cons b (cons c l))) -> Sorted (cons a (cons b l)).
  intros.
  miniinv H.
  apply Sorted_recursive.
  lia.
  miniinv H0.
  assumption.
Qed.

Theorem Sorted_min: forall n l, Sorted (cons n l) -> n <= min_def n l.
  intros.
  induction l.
  - simpl.
    lia.
  - miniinv H.
    miniinv U.
    simpl.
    pose proof (IHl U) as IH.
    destruct (min_def n l <? n0).
    exact IH.
    lia.
Qed.

Ltac miniinv2 H := try pose proof (Sorted_tail _ _ H) as ?H;
                   try pose proof (Sorted_min _ _ H) as ?Min;
                   try pose proof (Sorted_le _ _ _ H) as ?Le;
                   try pose proof (Sorted_under _ _ _ H) as ?U;
                   try pose proof (Sorted_under2 _ _ _ _ H) as ?dU.

Ltac miniinv H ::= miniinv2 H.

Fixpoint append (a b : List) : List := match a with
                              | nil => b
                              | cons h t => cons h (append t b)
                              end.

Theorem Sorted_append1 : forall a b, Sorted (append a b) -> Sorted a.
Proof.
  intros.
  destruct a.
  constructor.
  simpl in *.
  generalize dependent n.
  induction a; intros.
  constructor.
  simpl in *.
  miniinv H.
  constructor.
  exact Le.
  pose proof (IHa n H0) as IH.
  exact IH.
Qed.

Theorem Sorted_under_n: forall a m b, Sorted (append a (cons m b)) -> Sorted (append a b).
Proof.
  intros.
  generalize dependent b.
  induction a; intros.
  - simpl in H |- *.
    miniinv H.
    exact H0.
  - simpl in *.
    miniinv H.
    pose proof (IHa b H0) as IH.






Theorem emplace_spec: forall n l, Sorted l -> Sorted (emplace n l).
Proof.
  intros.
  destruct l.
    simpl. exact (Sorted_one _).
  simpl.
  destruct (n0 <? n) eqn:E.
  conv_ord.
  induction l.
  - simpl.
    apply Sorted_recursive;
    [lia | apply Sorted_one].
  - simpl.
    destruct (n1 <? n) eqn: E1.
    all: conv_ord.
    apply Sorted_recursive.
    miniinv H.
    lia.
    miniinv H.
    miniinv H0.
    pose proof (IHl U).
    miniinv H2.
