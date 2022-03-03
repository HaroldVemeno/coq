
Section Pierce.

  Parameter pierce : forall A B, ((A -> B) -> A) -> A.



  Theorem nnpp : forall A, ~~A -> A.
  Proof.
    intros A nna.
    unfold not in *.
    apply (pierce _ False).
    intro na.
    specialize (nna na).
    contradiction.
  Defined.


  Theorem pem : forall A, A \/ ~A.
  Proof.
    intros.
    apply (pierce _ False).
    unfold not in *.
    intro npem.
    right.
    intro a.
    apply npem.
    left.
    exact a.
  Defined.

  Definition pemd A: A \/ ~A := pierce (A \/ ~A) False (fun npem => or_intror (fun a => npem (or_introl a))).

  Theorem ip : forall A B : Prop, (A -> B) <-> (~B -> ~A).
  Proof.
    intros.
    split.
    intro ab.
    unfold not.
    intros nb a.
    apply nb, ab, a.
    intros nbna a.
    destruct (pem B) as [b | nb].
    exact b.
    specialize (nbna nb).
    contradiction.
  Defined.

  Compute pem.

End Pierce.
