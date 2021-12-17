Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.BinInt.
Require Import Lia ssreflect.
Open Scope Z_scope.

Definition list_max_Z : list Z -> Z := fold_right Z.max 0.

Lemma list_max_Z_spec : forall l,
  let max_val := list_max_Z l in
  Forall (fun x => x <= max_val) l /\
  (In max_val l \/ max_val = 0).
Proof. 
  intros.
  subst max_val.
  split.
  - induction l; [easy|].
    apply Forall_cons.
    + simpl.
      unfold Z.max.
      destruct (a ?= list_max_Z l) eqn:H; [easy| |easy].
      rewrite Z.compare_lt_iff in H.
      lia.
    + simpl.
      unfold Z.max.
      destruct (a ?= list_max_Z l) eqn:H.
      * rewrite Z.compare_eq_iff in H.
        rewrite H.
        exact IHl.
      * exact IHl.
      * rewrite Z.compare_gt_iff in H.
        apply Forall_forall.
        intros.
        rewrite Forall_forall in IHl.
        pose proof (IHl x).
        pose proof (H1 H0).
        pose proof (Z.le_lt_trans _ _ _ H2 H).
        lia.
  - induction l.
    + right. easy.
    + destruct IHl.
      * simpl.
        unfold Z.max.
        destruct (a ?= list_max_Z l).
        -- left. left. reflexivity.
        -- left. right. exact H.
        -- left. left. reflexivity.
      * simpl.
        unfold Z.max.
        destruct (a ?= list_max_Z l) eqn:H0.
        -- right. 
            rewrite Z.compare_eq_iff in H0.
            congruence.
        -- right. exact H. 
        -- left. left. reflexivity.
  (* Show Proof. *)
Qed.

Lemma list_max_Z_spec2 : forall l,
  let max_val := list_max_Z l in
  Forall (fun x => x <= max_val) l /\
  (In max_val l \/ max_val = 0).
Proof.
  intros.
  subst max_val.
  split.
  - apply Forall_forall.
    intros x I.
    induction l.
    + simpl in I. contradiction.
    + simpl in *. 
      destruct I as [-> | J].
      lia.
      pose proof (IHl J).
      lia.
  - induction l.
    simpl.
    right.
    reflexivity.
    simpl in *.
    destruct IHl;
    pose proof (Z.max_spec_le a (list_max_Z l));
    destruct H0 as [[L ->] | [A B]].
    auto.
    auto.
    auto.
    auto.


Abort.
      
             
Lemma list_max_Z_spec3 : forall l,
  let max_val := list_max_Z l in
  Forall (fun x => x <= max_val) l /\
  (In max_val l \/ max_val = 0).
Proof.
  move => l /=; split.
  - rewrite Forall_forall => x.
    by elim: l => //= h t IH [-> | /IH]; lia.
  - elim: l => //= [| h t]; first by right.
    by case: (Z.max_spec_le h (list_max_Z t)) => [] [H] -> []; auto.
    (* Show Proof. *)
Qed.

Lemma list_max_Z_spec4 : forall l,
  let max_val := list_max_Z l in
  Forall (fun x => x <= max_val) l /\
  (In max_val l \/ max_val = 0).
Proof.
  move => l /=; split.
  - rewrite Forall_forall => x.
    elim: l => //=.
    move=> h t IH.
    case=> [-> | /IH].
    lia.
    lia.
  - elim: l => //= [| h t]; first by right.
    by case: (Z.max_spec_le h (list_max_Z t)) => [] [H] -> []; auto.
    (* Show Proof. *)
Qed.
