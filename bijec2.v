Require Import Lia Arith.

Record iso (A B : Set) : Set :=
  bijection {
    A_to_B : A -> B;
    B_to_A : B -> A;
    A_B_A  : forall a : A, B_to_A (A_to_B a) = a;
    B_A_B  : forall b : B, A_to_B (B_to_A b) = b
  }.

Notation "x # y" := (prod x y) (at level 50, left associativity).

(* Cartesian power of a set. Zeroth power is the singleton set (unit). *)
Fixpoint set_power (A : Set) (n : nat) := match n with
  | O => unit
  | S n' => A # set_power A n'
  end.

Notation "x ^^ y" := (set_power x y) (at level 30).

(* Unlike Agda, Coq has a feature to print the definition of any variables, so
   you should copy your own solution for these properties if you want to use them.
   These theorems are not tested. *)

(* Any set has the same cardinality as itself. *)
Theorem iso_refl : forall A : Set, iso A A.
Proof.
  intros.
  apply (bijection _ _ (fun a => a) (fun a => a)).
  - intros.
    easy.
  - intros.
    easy.
Qed.


(* iso is symmetric. *)
Theorem iso_sym : forall A B : Set, iso A B -> iso B A.
Proof.
  intros.
  destruct H as [ab ba aba bab].
  apply (bijection B A ba ab bab aba).
Qed.

(* iso is transitive. *)
Theorem iso_trans : forall A B C : Set, iso A B -> iso B C -> iso A C.
Proof.
  intros.
  destruct H as [ab ba aba bab].
  destruct H0 as [bc cb bcb cbc].
  apply (bijection _ _ (fun a => bc (ab a)) (fun c => ba (cb c))).
  - intros.
    rewrite bcb.
    rewrite aba.
    easy.
  - intros.
    rewrite bab.
    rewrite cbc.
    easy.
Qed.

(* Given two functions A->B and B->A, if A->B->A is satisfied and B->A is injective, A <=> B. *)
Theorem bijection_alt : forall (A B : Set) (A2B : A -> B) (B2A : B -> A),
  (forall a, B2A (A2B a) = a) -> (forall b1 b2, B2A b1 = B2A b2 -> b1 = b2) -> iso A B.
Proof.
  intros.
  econstructor.
  - intros.
    apply H.
  - intros.
    simpl.
    apply H0.
    rewrite H.
    easy.
Qed.

Fixpoint isosi (n : nat) : (nat # nat) :=
  match n with
    | 0 => (0, 0)
    | S m => match isosi m with
              | (0, a) => (S a, 0)
              | (S b, a) => (b, S a)
             end
  end.

Fixpoint summy (n : nat) : nat :=
  match n with
    | 0 => 0
    | (S a) => n + summy a
  end.

Definition osiso (nn : nat # nat) : nat :=
  let '(a, b) := nn in b + summy (a + b).

(* Task 1. Prove that nat has the same cardinality as nat * nat. *)

Lemma summy_inj_gen : forall n m k, k*n + summy n = k*m + summy m -> n = m.
Proof.
  fix H 1.
  intros.
  destruct n.
  - simpl in *.
    destruct m.
    easy.
    simpl in H0.
    lia.
  - destruct m.
    simpl in H0.
    lia.
    simpl in H0.
    f_equal.
    apply (H n m (S k)).
    simpl.
    lia.
Qed.

Lemma summy_inj : forall n m, summy n = summy m -> n = m.
Proof.
  intros.
  pose proof (summy_inj_gen n m 0).
  simpl in H0.
  auto.
Qed.

Theorem nat_iso_natxnat : iso nat (nat # nat).
Proof.
  apply (bijection_alt _ _ isosi osiso).
  - intros.
    induction a.
    * easy.
    * simpl.
      destruct (isosi a).
      destruct n.
      simpl in *.
      rewrite Nat.add_0_r.
      lia.
      simpl in *.
      rewrite (Nat.add_comm n (S n0)).
      simpl.
      rewrite (Nat.add_comm n0 n).
      lia.
  - intros.
    unfold osiso in *.
    destruct b1, b2.
    revert n n0 n1 n2 H.
    fix H 1.
    intros.




(* Task 2. Prove that nat has the same cardinality as nat ^ n, where n is nonzero and finite. *)

Theorem nat_iso_nat_power : forall n, iso nat (nat ^^ S n).
Proof. Admitted.
