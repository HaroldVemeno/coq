Require Import ZArith.
Import Z.
Open Scope Z_scope.

(* Preloaded:

Require Import Preloaded.

*)

Require Import ZArith.
Import Z.

Fixpoint geom_sum (n : nat) (z : Z) : Z :=
  match n with
  | O => 1
  | S n' => z ^ of_nat n + geom_sum n' z
  end.

Open Scope Z_scope.

Definition geom_formula (n : nat) (z : Z) : Z :=
  if z =? 1 then succ (of_nat n)
  else (z ^ (succ (of_nat n)) - 1) / (z - 1).

Theorem geom_eq n z : geom_sum n z = geom_formula n z.
Proof.
  induction n.
  simpl.
  unfold geom_formula.
  simpl.
  unfold pow_pos.
  simpl.
  rewrite Z.mul_comm.
  assert (z = 1 \/ z <> 1).
  induction z.
  right.
  unfold "<>".
  intros.
  discriminate.
  induction p.
  destruct IHp.
  right.
