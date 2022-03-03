
Inductive pos := mkPos : (nat -> pos) -> pos.

Check pos_ind.


Fixpoint pos_ind0 (P: pos -> Prop)
    (f : forall p : nat -> pos, (forall n, P (p n)) -> P (mkPos p))
    (p : pos) {struct p} : P p
  := match p with
       mkPos np => f np (fun n => pos_ind0 P f (np n))
     end.

Theorem npos : pos -> False .
Proof.
  intros.
  induction H.
  apply H.
  apply 9.
Qed.
