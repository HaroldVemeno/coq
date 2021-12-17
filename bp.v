Require Import List Bool Setoid Lia.


Fact another_one : forall (X : Type) (l : list X) (f g : X -> bool),
  length (filter (fun x => f x && g x) l) <= length (filter f l) /\
  length (filter (fun x => f x && g x) l) <= length (filter g l).
Proof.
  split.
  induction l.
  auto.
  destruct (f a) eqn:hF.
  destruct (g a) eqn:hG.
  simpl.
  rewrite hF.
  rewrite hG.
  simpl.
  lia.
  simpl.
  rewrite hF.
  rewrite hG.
  simpl.
  lia.
  simpl.
  rewrite hF.
  simpl.
  lia.
  induction l.
  auto.
  destruct (f a) eqn:hF.
  destruct (g a) eqn:hG.
  simpl.
  rewrite hF.
  rewrite hG.
  simpl.
  lia.
  simpl.
  rewrite hF.
  rewrite hG.
  simpl.
  lia.
  destruct (g a) eqn:hG.
  simpl.
  simpl.
  rewrite hF.
  rewrite hG.
  simpl.
  lia.
  simpl.
  rewrite hF.
  rewrite hG.
  simpl.
  lia.
Qed.