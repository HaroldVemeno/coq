Require Import Classical.

Theorem drinker : forall (A : Set) (r : A -> Prop) (e : A),
  exists x, (r x -> forall y, r y).
Proof.
  intros.
  destruct (classic (forall y, r y)).
  exists e.
  intros.
  apply H.
  apply not_all_ex_not in H.
  destruct H.
  exists x.
  intro.
  contradiction.
  Show Proof.
Qed.

