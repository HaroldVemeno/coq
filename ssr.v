Require Import ssreflect ssrbool.

Goal forall A B, A /\ B -> B /\ A.
Proof.
    by move=> A B [].
Qed.

Goal forall A B, A \/ B -> B \/ A.
Proof.
    by move=> A B [a | b] ; [right | left].
Qed.

Goal forall (A B : bool), A \/ B -> B \/ A.
Proof.
    by move=> [] [] AoB; apply/orP; move/orP : AoB.
Qed.

Goal forall A (a : A) (P : A -> Prop),  (forall P : Prop, P \/ ~P) -> exists x, P x -> forall y, P y.
Proof.
    move=> A a P EP.
    case: (EP (exists u : A, ~P u)) => [[u nPu]| nenPu].
    by exists u.
    exists a => pa m.
    case: (EP (P m)) => // npm.
    by case: nenPu; exists m.
    Show Proof.
Qed.

