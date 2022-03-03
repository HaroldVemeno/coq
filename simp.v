(* Preloaded.v

   The key definitions and notations in this file are taken
   directly from the Software Foundations series, an
   excellent resource for learning Coq:
   https://softwarefoundations.cis.upenn.edu/current/index.html

   The copyright notice of the series is reproduced below as
   follows:

   Copyright (c) 2019

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to deal
   in the Software without restriction, including without limitation the rights
   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be included in
   all copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
   THE SOFTWARE. *)

(* Volume 1: Logical Foundations *)

(* Total and Partial Maps (Maps) *)

Require Export Coq.Strings.String.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
  (at level 100, v at next level, right associativity).

(* Simple Imperative Programs (Imp) *)

Require Import Coq.Arith.PeanoNat.

Definition state := total_map nat.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.
Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.
Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity) : imp_scope.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.
Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2 => (aeval st a1) <=? (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Definition empty_st := (_ !-> 0).

Notation "a '!->' x" := (t_update empty_st a x) (at level 100).

Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Bind Scope imp_scope with com.
Notation "'SKIP'" :=
   CSkip : imp_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : imp_scope.

Reserved Notation "st '=[' c ']=>' st'" (at level 40).
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ SKIP ]=> st
  | E_Ass : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ WHILE b DO c END ]=> st''->
      st =[ WHILE b DO c END ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

(* Volume 2: Programming Language Foundations *)

(* Program Equivalence (Equiv) *)

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state),
    beval st b1 = beval st b2.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').

Definition capprox (c1 c2 : com) : Prop :=
  forall (st st' : state),
  st =[ c1 ]=> st' -> st =[ c2 ]=> st'.

Open Scope imp_scope.

Definition seq_if_dist_r := forall b c1 c2 c3, cequiv
  (TEST b THEN c1 ;; c3 ELSE c2 ;; c3 FI)
  (TEST b THEN c1 ELSE c2 FI ;; c3).

Theorem seq_if_dist_r_dec :
  seq_if_dist_r \/ ~ seq_if_dist_r.
Proof.
  left.
  intros b c1 c2 c3 st st'.
  split.
  - intros H.
    inversion H; subst;
    inversion H6; subst;
    eauto using ceval.
  - intros H.
    inversion H; subst;
    inversion H2; subst;
    eauto using ceval.
Qed.

Definition seq_if_dist_l := forall b c1 c2 c3, cequiv
  (TEST b THEN c1 ;; c2 ELSE c1 ;; c3 FI)
  (c1 ;; TEST b THEN c2 ELSE c3 FI).

Theorem seq_if_dist_l_dec :
  seq_if_dist_l \/ ~ seq_if_dist_l.
Proof.
  right.
  intros ns.
  hnf in ns.
  specialize (ns (X = 0) (X ::= 100) (Y ::= 1) (Y ::= 2)).
  hnf in ns.
  specialize (ns (X !-> 0)).
  epose proof (ns _).
  clear ns.
  destruct H.
  clear H0.
  unshelve epose proof (H _).
  constructor.
  simpl.
  reflexivity.
  econstructor.
  constructor.
  simpl.
  reflexivity.
  econstructor.
  simpl.
  reflexivity.
  clear H.
  inversion H0; subst; clear H0.
  inversion H5; subst; clear H5;
  inversion H2; subst; clear H2;
  simpl in *.
  easy.
  inversion H7; subst; clear H7.
  inversion H3; subst; clear H3.
  remember (Y !-> 2; X !-> 100; X !-> 0) as a.
  remember (a Y) as b.
  pose proof Heqb.
  rewrite Heqa in Heqb.
  compute in Heqb.
  rewrite H0 in H.
  compute in H.
  subst.
  easy.
Qed.

Require Import FunctionalExtensionality.

Definition cmax_exists := exists cmax, forall c, capprox c cmax.

Lemma deterministic : forall st bst cst c,
    st =[ c ]=> bst -> st =[ c ]=> cst -> bst = cst.
Proof.
  intros.
  revert H0 H.
  generalize dependent cst.
  generalize dependent bst.
  generalize dependent st.
  induction c; intros;
  inversion H; inversion H0; subst; clear H H0; try congruence; try eauto.
  pose proof (IHc1 st st' st'0 ltac:(easy) ltac:(easy)); subst.
  eapply IHc2; eauto.
  pose proof (IHc st st'0 st' ltac:(easy) ltac:(easy)); subst.
  revert bst cst H7 H14.
  generalize st'.
  fix H 4.
  intros.
  inversion H7; inversion H14; subst; clear H7 H14.
  reflexivity.
  rewrite  H6 in H12.
  discriminate.
  rewrite  H2 in H17.
  discriminate.
  pose proof (IHc st'0 st'1 st'2 ltac:(easy) ltac:(easy)); subst.
  eapply H.
  apply H9.
  apply H19.
Qed.

Notation infer := ltac:(assumption) (only parsing).

Theorem cmax_exists_dec : cmax_exists \/ ~ cmax_exists.
Proof.
  right.
  intros H.
  hnf in H.
  destruct H.
  pose proof H.
  evar (c : com).
  evar (d : com).
  specialize (H c).
  specialize (H0 d).
  unfold capprox in *.
  evar (st : state).
  evar (stc : state).
  evar (std : state).
  specialize (H st stc).
  specialize (H0 st std).
  instantiate (st := empty_st).
  instantiate (c := (X ::= 6)).
  instantiate (d := (X ::= 9)).
  unshelve epose proof (H0 _) as H0.
  constructor.
  simpl.
  reflexivity.
  unshelve epose proof (H _) as H.
  constructor.
  simpl.
  reflexivity.
  assert (std <> stc).
    intros ss.
    assert (stc X = std X) by congruence.
    compute in H1.
    easy.
  pose proof (deterministic st stc std x infer infer).
  congruence.
Qed.
