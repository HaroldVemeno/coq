Require Import ssreflect.
Theorem frobenius (A : Set) (P : A -> Prop) (Q : Prop) :
  (exists x : A, Q /\ P x) <-> (Q /\ exists x : A, P x).
Proof.
  split=> [[x [q px]]|[q [x px]]].
  - split => //. by exists x.
  - by exists x.
Qed.
