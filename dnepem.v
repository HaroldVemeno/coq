Definition axiom_pem := forall (P : Prop), P \/ ~P.

Definition axiom_dne := forall (P : Prop), ~ ~P -> P.

Theorem to : axiom_pem -> axiom_dne.
Proof.
  intros a P nnp.
  destruct (a P) as [p | np].
  - exact p.
  - contradiction.
Qed.

Theorem from : axiom_dne -> axiom_pem.
Proof.
  intros a P.
  compute in a.
  assert (~~(~P \/ ~~P)).
    unfold not in *.
    intros.
    apply H.
    right.
    intro.
    apply H.
    left.
  exact H0.
  apply a in H.
  destruct H.
  right. exact H.
  apply a in H.
  left. exact H.
Qed.
