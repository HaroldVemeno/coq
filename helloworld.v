Goal forall X Y : Prop, X -> Y -> X.
Proof.
  intros X Y.
  intros A.
  intros B.
  assumption.
Qed.

Goal forall X : Prop, X <-> X.
Proof.
  intros X.
  split.

  intros A.
  assumption.
  intros A.
  assumption.
Qed.

Goal forall X : Prop, False -> X -> False.
  Proof.
    intros X A B.
    assumption.
Qed.

Goal forall X Y : Prop, (X -> Y) -> ~Y -> ~X.
Proof.
  intros X Y xy ny.
  intro x.
  apply xy in x.
  contradiction.
  Show Proof.
Qed.

Goal forall X Y Z : Prop, (X -> Y) /\ (Y -> Z) -> (X -> Z).
Proof.
  intros X Y Z.
  intros xy_and_yz.
  intros x.
  destruct xy_and_yz as [xy yz].
  apply xy in x. apply yz in x.
  apply x.
Qed.

Goal forall P Q R : Prop, (P /\ (Q \/ R)) -> ((P /\ Q) \/ (P /\ R)).
Proof.
  intros.
  destruct H as [p [q|r]].
  left.
  split.
  apply p.
  apply q.
  right.
  split.
  apply p.
  apply r.
Qed.

Goal forall P Q R S : Prop, ((P -> Q) /\ (R -> S) /\ (~Q \/ ~S)) -> (~P \/ ~R).
Proof.
  intros P Q R S.
  intro H.
  destruct H as [p_to_q [r_to_s nq_or_ns]].
  destruct nq_or_ns as [nq | ns].
  left.
  intro p.
  apply p_to_q in p.
  contradiction.
  right.
  intro r.
  apply r_to_s in r.
  contradiction.
Qed.

Goal forall P Q R : Prop, ((P -> Q) /\ (P -> R)) -> (P -> (Q /\ R)).
Proof.
  intros P Q R.
  intro H.
  destruct H as [pq pr].
  intro p.
  split.
  apply pq in p.
  assumption.
  apply pr in p.
  assumption.
Qed.


Goal forall P Q R : Prop, (P -> (Q -> R)) -> ((P -> Q) -> (P -> R)).
Proof.
  intros P Q R.
  intros pqr pq p.
  assert Q as q.
  apply pq in p.
  apply p.
  apply pqr in p.
  apply p.
  apply q.
  Show Proof.
Qed.

Goal forall P Q R : Prop, (P -> (Q -> R)) -> ((P -> Q) -> (P -> R)).
Proof.
  intros P Q R.
  intros pqr pq p.
  apply pqr.
  apply p.
  apply pq.
  apply p.
  Show Proof.
Qed.

Goal forall P Q R : Prop, (P -> (Q -> R)) -> ((P -> Q) -> (P -> R)).
Proof.
  intros P Q R.
  exact (fun pqr pq p => pqr p (pq p)).
  Show Proof.
Qed.

Inductive Bool : Set
  := true  : Bool
   | false : Bool .

Definition to_prop (b : Bool) :=
  match b with
   | true => True
   | false => False
  end.
