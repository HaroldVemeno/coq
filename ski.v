Set Implicit Arguments.

Inductive SKI : Type :=
  | S
  | K
  | I
  | App : SKI -> SKI -> SKI.

Declare Custom Entry ski_expr.
Notation "[[ e ]]" := e (e custom ski_expr at level 2).
Notation "x y" := (App x y) (in custom ski_expr at level 1, left associativity).
Notation "( x )" := x (in custom ski_expr, x at level 2).
Notation "'S'" := S (in custom ski_expr at level 0).
Notation "'K'" := K (in custom ski_expr at level 0).
Notation "'I'" := I (in custom ski_expr at level 0).
Notation "{ x }" := x (in custom ski_expr at level 0, x constr).
Notation "x" := x (in custom ski_expr at level 0, x ident).

Reserved Notation "x ==> y" (at level 90, no associativity).

Inductive red_step : SKI -> SKI -> Prop :=
  | red_S : forall a b c, [[S a b c]] ==> [[a c (b c)]]
  | red_K : forall a b, [[K a b]] ==> [[a]]
  | red_I : forall a, [[I a]] ==> [[a]]
  | red_head : forall a a' b, [[a]] ==> [[a']] -> [[a b]] ==> [[a' b]]
  | red_tail : forall a b b', [[b]] ==> [[b']] -> [[a b]] ==> [[a b']]
where "x ==> y" := (red_step x y).

Inductive rtc (T : Type) (rel : T -> T -> Prop) : T -> T -> Prop :=
  | rtc_refl (a : T) : rtc rel a a
  | rtc_trans1 (a b c : T) : rel a b -> rtc rel b c -> rtc rel a c.

Definition red_rtc := rtc red_step.
Notation "x ==>* y" := (red_rtc x y) (at level 90, no associativity).

Hint Constructors red_step : core.
Hint Constructors rtc : core.
Hint Unfold red_rtc : core.

(* Notations for expressing a term is extensionally equal to T or F, respectively. *)
Notation "t ~~>*T" := (forall x y, [[{t} x y]] ==>* [[x]]) (at level 90, only parsing).
Notation "t ~~>*F" := (forall x y, [[{t} x y]] ==>* [[y]]) (at level 90, only parsing).
(*

\ab.ba
[\a.[\b.ba]]
[\a.SI(Ka)]
S(K(SI))K
 *)
Ltac reduce :=
  match goal with
    | |- ?a ==>* ?a => apply rtc_refl
    | |- _ ==>* _ => eapply rtc_trans1
    | |- [[K {_} {_}]] ==> _ => apply red_K
    | |- [[S {_} {_} {_}]] ==> _ => apply red_S
    | |- [[I {_}]] ==> _ => apply red_I
  end.

(*
rev x f := f x *)


Definition rev : SKI := [[ S (K (S I)) K ]].
Theorem rev_correct : forall f x, [[{rev} x f]] ==>* [[f x]].
Proof.
  intros.
  unfold rev.
  eapply rtc_trans1.
  constructor.
  constructor.
  eapply rtc_trans1.
  constructor.
  constructor.
  constructor.
  eapply rtc_trans1.
  constructor.
  eapply rtc_trans1.
  constructor.
  constructor.
  eapply rtc_trans1.
  apply red_tail.
  constructor.
  constructor.
Qed.

Require Import Nat.

Inductive Lam : Set :=
  | Abstr : Lam -> Lam
  | Appl : Lam -> Lam -> Lam
  | Var : nat -> Lam.

Fixpoint len l : nat :=
  match l with
    | Abstr a => 1 + len a
    | Appl a b => len a + len b
    | Var _ => 1
  end.

Definition LS := Abstr (Abstr (Abstr (Appl (Appl (Var 2) (Var 0)) (Appl (Var 1) (Var 0))))).
Definition LK := Abstr (Abstr (Var 1)).
Definition LI := Abstr (Var 0).

Fixpoint unskify s : Lam :=
  match s with
    | App a b => Appl (unskify a) (unskify b)
    | S => LS
    | K => LK
    | I => LI
  end.

Fixpoint skify_i (n : nat) (l : Lam) : Lam := match n with 0 => l | Datatypes.S m =>
  match l with
    | Abstr (Abstr l) => skify_i m (Abstr (skify_i m (Abstr l)))
    | Abstr (Var 0) => LI
    | Abstr (Var (Datatypes.S a)) => Appl LK (Var a)
    | Abstr (Appl a b) => Appl (Appl LS (skify_i m a)) (skify_i m b)
    | Appl a b => Appl (skify_i m a) (skify_i m b)
    | Var i => Var i
  end end.

Definition skify l: Lam := let ln := len l in skify_i 10000 l.

Fixpoint SKIfy l: SKI :=
  match l with
    | Abstr (Abstr (Abstr (Appl (Appl (Var 2) (Var 0)) (Appl (Var 1) (Var 0))))) => S
    | Abstr (Abstr (Var 1)) => K
    | Abstr (Var 0) => I
    | Appl a b => App (SKIfy a) (SKIfy b)
    | _ => [[I I I]] end.


(* B f g x := f (g x) *)
Definition B : SKI := SKIfy (skify (Abstr (Abstr (Abstr (Appl (Var 2) (Appl (Var 1) (Var 0))))))).
Print B.
Theorem B_correct : forall f g x, [[{B} f g x]] ==>* [[f (g x)]].
Proof.
  intros.
  unfold B.
  simpl.

(* C f x y := f y x *)
Definition C : SKI. Admitted.
Theorem C_correct : forall f x y, [[{C} f x y]] ==>* [[f y x]].
Proof. Admitted.

(* rotr y f x := f x y *)
Definition rotr : SKI. Admitted.
Theorem rotr_correct : forall f x y, [[{rotr} y f x]] ==>* [[f x y]].
Proof. Admitted.

(* rotv x y f := f x y *)
Definition rotv : SKI. Admitted.
Theorem rotv_correct : forall f x y, [[{rotv} x y f]] ==>* [[f x y]].
Proof. Admitted.

(* Y f := (\x. f (x x)) (\x. f (x x)) *)
(* The Y combinator has the property `Y f = f (Y f)`, but we can't prove it with direct reduction.
   Instead, we prove that both sides reduce to the same term. *)
Definition Y : SKI. Admitted.
Theorem Y_correct : forall f, exists t, ([[{Y} f]] ==>* t) /\ ([[f ({Y} f)]] ==>* t).
Proof. Admitted.

(* Boolean logic. Church booleans are used. *)
(* T x y := x *)
(* F x y := y *)
Definition T : SKI. Admitted.
Theorem T_correct : forall x y, [[{T} x y]] ==>* [[x]].
Proof. Admitted.

Definition F : SKI. Admitted.
Theorem F_correct : forall x y, [[{F} x y]] ==>* [[y]].
Proof. Admitted.

(* Notations for expressing a term is extensionally equal to T or F, respectively. *)
Notation "t ~~>*T" := (forall x y, [[{t} x y]] ==>* [[x]]) (at level 90, only parsing).
Notation "t ~~>*F" := (forall x y, [[{t} x y]] ==>* [[y]]) (at level 90, only parsing).

Definition Not : SKI. Admitted.
Theorem NotT_F : [[{Not} {T}]] ~~>*F.
Proof. Admitted.
Theorem NotF_T : [[{Not} {F}]] ~~>*T.
Proof. Admitted.

Definition And : SKI. Admitted.
Theorem AndTT_T : [[{And} {T} {T}]] ~~>*T.
Proof. Admitted.
Theorem AndTF_F : [[{And} {T} {F}]] ~~>*F.
Proof. Admitted.
Theorem AndFT_F : [[{And} {F} {T}]] ~~>*F.
Proof. Admitted.
Theorem AndFF_F : [[{And} {F} {F}]] ~~>*F.
Proof. Admitted.

Definition Or : SKI. Admitted.
Theorem OrTT_T : [[{Or} {T} {T}]] ~~>*T.
Proof. Admitted.
Theorem OrTF_T : [[{Or} {T} {F}]] ~~>*T.
Proof. Admitted.
Theorem OrFT_T : [[{Or} {F} {T}]] ~~>*T.
Proof. Admitted.
Theorem OrFF_F : [[{Or} {F} {F}]] ~~>*F.
Proof. Admitted.

Definition Xor : SKI. Admitted.
Theorem XorTT_F : [[{Xor} {T} {T}]] ~~>*F.
Proof. Admitted.
Theorem XorTF_T : [[{Xor} {T} {F}]] ~~>*T.
Proof. Admitted.
Theorem XorFT_T : [[{Xor} {F} {T}]] ~~>*T.
Proof. Admitted.
Theorem XorFF_F : [[{Xor} {F} {F}]] ~~>*F.
Proof. Admitted.
