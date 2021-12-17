Require Import PeanoNat Bool BoolEq Nat.

Open Scope nat_scope.
Open Scope bool_scope.

Definition impossible := idProp.

Inductive Bad : Type :=
  | Bad1 (i : Bad) : Bad
  | Bad2 (i : Bad) (j : Bad) : Bad
  | Bad3 (i : Bad) (a : nat): Bad.

Theorem Bad_explosion : Bad -> False.
  intros b.
  induction b.
  exact IHb.
  exact IHb1.
  exact IHb.
Qed.

Inductive Option (A : Type) : bool -> Type :=
  | Some (a : A) : Option A true
  | None : Option A false.

Arguments Some {A}.
Arguments None {A}.

Definition unwrap (o : Option nat true) : nat :=
  match o with
    | Some a => a
  end.

Definition map {b : bool} (o : Option nat b) (f : nat -> nat): Option nat b :=
  match o with
    | Some a => Some (f a)
    | None => None
  end.

Definition add2 {b : bool} : Option nat b -> Option nat b -> Option nat b :=
  match b with
    | true => fun (o p: Option nat true) => Some (unwrap o + unwrap p)
    | false => fun (o p: Option nat false) => None
  end.

Definition nebo {b c : bool} : Option nat b -> Option nat c -> Option nat (b || c) :=
  match b, c with
    | false, false => fun _ _ => None
    | true, _ => fun a _ => a
    | false, true => fun _ a => a
  end.

Eval compute in unwrap (nebo (nebo (Some 4) None) (None)).

Section stuff.

  Parameter u v : bool.
  Parameter a : Option nat u.
  Parameter b : Option nat v.

  Eval cbn in nebo (nebo (None) b) a.
  Fail Eval cbn in unwrap (nebo (nebo (None) b) a).
  Eval cbn in unwrap (nebo (nebo (Some 8) b) a).
  Fail Eval cbn in unwrap (nebo (nebo b (Some 9)) a).

  Theorem ol {p} : Option nat (p || true) = Option nat true.
  Proof.
    rewrite orb_true_r.
    easy.
  Qed.


  Lemma uw2 {p q}: Option nat (p || true || q) -> nat.
    intros H.
    repeat progress (rewrite orb_true_r in H; simpl in H).
    exact (unwrap H).
  Defined.

  Ltac unwrap_red H :=
    repeat progress (rewrite orb_true_r in H; simpl in H);
    exact H.

  Eval compute in uw2 ((fun H => ltac:(unwrap_red H)) (nebo (nebo None (Some 9)) None)).

  Eval cbn in unwrap ( nebo (nebo (Some 0) None) (Some 5) ).
  Eval cbn in unwrap ( nebo (nebo None None) (Some 5) ).
  Eval cbn in unwrap ( nebo (nebo (Some 0) None) None ).
  Eval cbn in unwrap ( nebo (nebo None (Some 85)) None ).
  Fail Eval cbn in unwrap ( nebo (nebo None None) None ).


End stuff .

Definition test {d : bool} (a b : Option nat d) : nat :=
  unwrap (nebo (nebo (Some 0) b) a).


Definition div (n d : nat) : if 0 <? d then nat else unit :=
  if 0 <? d as c return if c then nat else unit
  then n / d
  else tt.

Inductive Vec (A : Type) : nat -> Type :=
  | nil : Vec A 0
  | cons {n : nat} (head : A) (tail : Vec A n) : Vec A (S n).

Arguments nil {A}.
Arguments cons {A} {n}.

Definition uncons {A n} (a : Vec A (S n)) : A * Vec A n :=
  match a with
    cons h t => (h, t)
  end.

Fixpoint zip {A B n} : Vec A n -> Vec B n -> Vec (A * B) n :=
  match n with
    | 0 => fun _ _ => nil
    | S m => fun a b => match uncons a, uncons b with
                      | (ah, aa), (bh, bb) => cons (ah, bh) (zip aa bb)
                    end
  end.

Fixpoint foldr {A B n} (f : A -> B -> B) (b : B) (v : Vec A n) {struct v}: B :=
  match v with
    | nil  => b
    | cons e es => f e (foldr f b es)
  end.

Definition foldr1 {A n} (f : A -> A -> A) (v : Vec A (S n)) : A :=
  let '(b, bs) := uncons v
  in foldr f b bs.

Fixpoint foldl {A B n} (f : B -> A -> B) (b : B) (v : Vec A n) {struct v}: B :=
  match v with
    | nil  => b
    | cons e es=> foldl f (f b e) es
  end.

Definition foldl1 {A n} (f : A -> A -> A) (v : Vec A (S n)) : A :=
  let '(b, bs) := uncons v
  in foldl f b bs.

Definition testvec := cons 5 (cons 1 (cons 9 (cons 4 (nil)))).

Definition flip {A B C} (f: A -> B -> C) (b : B) (a : A) : C := f a b.

Eval cbn in foldl1 (fun a b => a + b) testvec.
Eval cbn in foldr1 (fun a b => a + b) testvec.
