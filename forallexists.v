Definition pull (T : Type) (P : T -> Prop) : Type := (forall x : T, P x) -> {x : T | P x}.
Definition existence (T : Type) : Type := {x : T | True}.



Theorem cannot_pull : (forall T P, pull T P) -> False.
Proof.
  unfold pull.
  intros.
  specialize (X False (fun _=> False)).
  simpl in X.
  destruct X.
  intros.
  assumption.
  assumption.
  Show Proof.
 Qed.

Theorem but_why : exists T P, pull T P -> False.
Proof.
  exists False, (fun _ => False).
  unfold pull.
  intros.
  destruct H.
  intros. assumption.
  assumption.
Qed.

Theorem can_pull_if_existence : forall T, existence T -> (forall P, pull T P).
Proof.
  unfold existence.
  unfold pull.
  intros.
  destruct X.
  exists x.
  apply H.
Qed.

Theorem existence_if_can_pull : forall T, (forall P, pull T P) -> existence T.
Proof.
  unfold existence.
  unfold pull.
  intros.
  specialize (X (fun _ => True)).
  simpl in X.
  apply X.
  intro.
  apply I.
Qed.

