Require Import Basics PeanoNat Bool Arith Nat.

Inductive List : Set :=
  | nil : List
  | cons (n : nat) (tail : List) : List.

Fixpoint length (l : List) : nat := match l with
  | nil => 0
  | cons _ rest => 1 + length rest
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

Fixpoint elem (n : nat) (l : List) : bool :=
  match l with
   | [] => false
   | m +> r => if m =? n then true else elem n r
  end.

Fixpoint count (n : nat) (l : List) : nat :=
  match l with
  | nil => 0
  | cons m lr => (if m =? n then 1 else 0) + count n lr
  end.

Inductive Perm : List -> List -> Prop :=
  | Perm_refl (a : List) : Perm a a
  | Perm_swap (n m : nat) (a b : List) (p : Perm a b) : Perm (n +> m +> a) (m +> n +> b)
  | Perm_cons (n : nat) (a b : List) (p : Perm a b): Perm (n +> a) (n +> b)
  | Perm_trans (a b c: List) (p : Perm a b) (q : Perm b c): Perm a c.

Theorem Perm_sym a b : Perm a b -> Perm b a.
Proof.
  intros.
  induction H.
  (* all: eauto using Perm.*)
  constructor.
  constructor.
  assumption.
  constructor.
  assumption.
  econstructor.
  eassumption.
  eassumption.
Qed.

Ltac Perm_auto :=
  match goal with
    | |- Perm ?a ?a  =>
        idtac "refl";
        apply Perm_refl;
        Perm_auto
    | |- Perm (?a +> _) (?a +> _) =>
        idtac "cons";
        apply Perm_cons;
        Perm_auto
    | |- Perm (?a +> ?b +> _) (?b +> ?a +> _) =>
        idtac "swap";
        apply Perm_swap;
        Perm_auto
    | |- Perm ?l (?a +> _) =>
        assert (elem a l = true) as _ by reflexivity;
        idtac "trans";
        eapply Perm_trans;
        repeat match goal with
          | |- Perm (?b +> a +> _) _ =>
              idtac "- swap";
              apply Perm_swap
          | |- Perm (?b +> _) _ =>
              idtac "- cons";
              apply Perm_cons
          | |- Perm [] [] =>
              idtac "- refl";
              apply Perm_refl
        end;
        Perm_auto
    | |- _ => idtac "end"
    end.

Goal Perm [3;5;2;6] [6;5;2;3].
  Perm_auto.
Qed.

Goal Perm [1;2;3;4;5;6;7;8;9] [1;9;3;2;7;6;5;4;8].
  Perm_auto.
Qed.



Theorem Perm_count a b: Perm a b -> forall n, count n a = count n b.
Proof.
  intros.
  induction H.
  easy.
  simpl.
  rewrite IHPerm.
  do 2 rewrite Nat.add_assoc.
  f_equal.
  rewrite Nat.add_comm.
  easy.
  simpl.
  rewrite IHPerm.
  easy.
  congruence.
Qed.
