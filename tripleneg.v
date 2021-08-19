Theorem not_not_not : forall P, ~~~P -> ~P.
Proof.
  intros.
  intro.
  unfold not in H.
  apply H.
  intros.
  apply H1 in H0.
  assumption.
Qed.
