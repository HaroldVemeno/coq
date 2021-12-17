Require Import Arith Classical Lia.
Import Nat.

Lemma sub_distr_l n a b : n * (a - b) = n * a - n * b.
Proof.
    induction n.
    compute. reflexivity.
    simpl.
    apply (plus_minus (a + n * a) (b + n * b) (a - b + n * (a - b))).
    rewrite -> IHn.
    rewrite Nat.add_assoc.
    symmetry.
    rewrite Nat.add_comm.
    rewrite Nat.add_assoc.
    




Theorem bin a b : a^3 + b^3 = (a + b) * (a^2 - a*b + b^2).
Proof.
    unfold "^".
    repeat rewrite Nat.mul_1_r.
    repeat rewrite Nat.mul_assoc.
    rewrite Nat.mul_add_distr_l.
    rewrite Nat.mul_add_distr_r.
    rewrite Nat.mul_add_distr_r.
    repeat rewrite Nat.mul_assoc.


Qed.

Theorem easy_fermat (a b c : nat) :
  a ^ 3 + b ^ 3 = c ^ 3 -> (3 | a * b * c).
Proof. Admitted.