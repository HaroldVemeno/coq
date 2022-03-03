
CoInductive stream (A : Set) : Set :=
  | cons : A -> stream A -> stream A.
Arguments cons {_} hd tl.

Notation "x :: y" := (cons x y) (at level 60, right associativity).

Definition head {A} (x : stream A) := match x with
  hd :: _ => hd end.
Definition tail {A} (x : stream A) := match x with
  _ :: tl => tl end.

CoInductive bisim {A : Set} (x y : stream A) : Set :=
  | bisim_eq : head x = head y -> bisim (tail x) (tail y) -> bisim x y.
Notation "x == y" := (bisim x y) (at level 70).


Module Introduction.

  (* Infinite sequence of ones. (not tested) *)
  CoFixpoint ones : stream nat := 1 :: ones.

  (* Infinite sequence of given value. *)
  CoFixpoint repeat {A : Set} (a : A) : stream A.
    constructor.
    assumption.
    auto.
  Defined.

  CoFixpoint even {A : Set} (x : stream A) : stream A.
    destruct x.
    constructor.
    assumption.
    apply even.
    destruct x.
    assumption.
  Defined.

  (* Elements at even and odd indexes, respectively. *)
  Definition odd {A : Set} (x : stream A) : stream A.
    destruct x.
    apply even.
    assumption.
  Defined.

  (* A stream equals its head plus its tail. (not tested) *)
  Lemma stream_unfold : forall {A : Set} (a : stream A), a = head a :: tail a.
  Proof. intros A a. destruct a. reflexivity. Qed.

End Introduction.

Module Bisimulation.

  Export Introduction.

  (* Bisimulation is reflexive. *)
  Theorem bisim_refl : forall {A : Set} (a : stream A), a == a.
  Proof.
    cofix H.
    intros.
    constructor.
    easy.
    auto.
  Defined.

Hint Resolve bisim_refl.

  (* Odd is tail of Even. *)
  (* Hint: Do you really need cofix? It may depend on your own definition of odd and even. *)
  Theorem odd_even : forall {A : Set} (x : stream A), odd x == even (tail x).
  Proof.
    intros.
    constructor.
    destruct x.
    simpl.
    easy.
    destruct x.
    simpl.
    auto.
  Defined.

End Bisimulation.

Module Merge.

  Export Bisimulation.

  (* Interleave two streams, starting with the left one. *)
  CoFixpoint merge {A : Set} (x y : stream A) : stream A.
    destruct x, y.
    constructor.
    exact a.
    constructor.
    exact a0.
    apply (merge _ x y).
  Defined.


  (* Main task: Merge even and odd, and get the original. *)
  Theorem moe : forall {A : Set} (a : stream A), merge (even a) (odd a) == a.
  Proof.
    cofix moe.
    intros.
    constructor.
    rewrite (stream_unfold (a)).
    simpl.
    rewrite (stream_unfold (tail a)).
    easy.
    constructor.
    rewrite (stream_unfold (a)).
    simpl.
    rewrite (stream_unfold (tail a)).
    simpl.
    easy.
    simpl.
    rewrite (stream_unfold (a)).
    simpl.
    rewrite (stream_unfold (tail a)).
    simpl.
    pose proof (moe A (tail (tail a))).
    rewrite (stream_unfold (tail (tail a))) in *.
    simpl.
    exact H.
  Defined.
End Merge.
