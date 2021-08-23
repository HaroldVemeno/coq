Require Import Setoid.

Theorem not_not_not : forall P, ~~~P <-> ~P.
Proof.
  split.
  intros.
  unfold not in *.
  intro.
  apply H.
  intros.
  apply H1.
  apply H0.
  unfold not.
  intros.
  apply (H0 H).
Qed.

Theorem wierd : forall P, ~(~P /\ ~~P).
Proof.
  intros P H.
  destruct H as [A B].
  apply (B A).
Qed.

Theorem www : forall P Q, ~(~P /\ ~Q) <-> ~~(~~P \/ ~~Q).
  Proof.
  intros.
  split.

  intro And.
  unfold not in *.
  intro Or.
  apply And.
  split;
    intro aPQ;
    apply Or;
    [left | right];
    intro nPQ;
    apply (nPQ aPQ).
  intro Or.
  intro And.
  unfold not in *.
  apply Or.
  intro Or0.
  destruct Or0 as [Or1 | Or1];
    apply Or1;
    apply And.
Qed.


Theorem wierder : forall P, ~~(~P \/ ~~P).
Proof.
  intros P.                    
  unfold not at 1 2 4 5.
  rewrite <- not_not_not in |- *.
  apply www.
  unfold not.
  intro And.
  destruct And as [nnP nP].
  apply (nnP nP).
Qed.

Theorem PP : forall P, ((~P)->~~P)->~~P.
Proof.
  intros.
  unfold not in *.
  intro.
  apply (H H0 H0).
Qed.

Theorem PPP : forall P, (P \/ ~P) -> ((~P)->P)->P.
Proof.
  intros.
  case H.
  intro.
  apply H1.
  exact H0.
Qed.
