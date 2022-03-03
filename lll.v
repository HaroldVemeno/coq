Fixpoint plus a b :=
  match a with
  | 0 => b
  | S a' => S (plus a' b)
  end.

Notation "a + b" := (plus a b) (left associativity, at level 50) : nat_scope.

Lemma plus_komut a b: a + b = b + a.
Proof.
  induction a.
  - simpl.
    induction b.
    + simpl.
      reflexivity.
    + simpl.
      rewrite <- IHb.
      reflexivity.
  - simpl.
    rewrite -> IHa. clear IHa.
    induction b.
    + simpl.
      reflexivity.
    + simpl.
      rewrite <- IHb.
      reflexivity.
Defined.

Lemma plus_asoc a b c: a + (b + c) = (a + b) + c.
Proof.
  induction a.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHa.
    reflexivity.
Defined.

Lemma plus_komut_u a b c: c + a + b = c + b + a.
Proof.
  rewrite <- plus_asoc.
  rewrite (plus_komut a b).
  rewrite plus_asoc.
  reflexivity.
Defined.

Fixpoint krát a b :=
  match a with
  | 0 => 0
  | S a' => plus b (krát a' b)
  end.

Notation "a * b" := (krát a b) (left associativity, at level 40) : nat_scope.

Lemma krát_komut a b: a * b = b * a.
Proof.
  induction a.
  - simpl.
    induction b.
    + simpl.
      reflexivity.
    + simpl.
      rewrite <- IHb.
      reflexivity.
  - simpl.
    rewrite -> IHa. clear IHa.
    induction b.
    + simpl.
      reflexivity.
    + simpl.
      rewrite <- IHb; clear IHb.
      repeat rewrite plus_asoc.
      rewrite (plus_komut b a).
      reflexivity.
Defined.

Lemma r_distrib a b c : a * (b + c) = a * b + a * c.
Proof.
  induction a.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHa.
    repeat rewrite plus_asoc.
    f_equal.
    rewrite <- plus_asoc.
    rewrite (plus_komut c) .
    repeat rewrite plus_asoc.
    reflexivity.
Defined.

Lemma l_distrib a b c : (a + b) * c = a * c + b * c.
Proof.
  rewrite krát_komut.
  rewrite (krát_komut a).
  rewrite (krát_komut b).
  apply r_distrib.
Defined.

Lemma krát_asoc a b c: a * (b * c) = (a * b) * c.
Proof.
  induction a.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHa.
    symmetry.
    rewrite (krát_komut _ c).
    rewrite (r_distrib c).
    rewrite (krát_komut c (a * b)).
    rewrite krát_komut.
    reflexivity.
Defined.

Lemma krát_komut_u a b c: c * a * b = c * b * a.
Proof.
  rewrite <- krát_asoc.
  rewrite (krát_komut a b).
  rewrite krát_asoc.
  reflexivity.
Defined.

Require Import Arith.

Definition mynatsrth : semi_ring_theory 0 1 plus krát eq :=
  {|
    SRadd_0_l := fun _ => eq_refl;
    SRadd_comm := plus_komut;
    SRadd_assoc := plus_asoc;
    SRmul_1_l := fun n => plus_komut n 0;
    SRmul_0_l := fun _ => eq_refl;
    SRmul_comm := krát_komut;
    SRmul_assoc := krát_asoc;
    SRdistr_l := l_distrib
 |}.

Add Ring mynatsr: mynatsrth.

Goal forall a b, a + b + 4 = a + 4 + b.
  intros.
  ring_simplify.
