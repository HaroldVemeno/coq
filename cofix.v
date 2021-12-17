Require Import Nat.

Set Primitive Projections.
Set Implicit Arguments.

CoInductive Stream (A : Set) : Set := 
    mkStream {head : A; tail : Stream A}.

Definition NatStream := Stream nat.

CoFixpoint zeroes : NatStream := 
    {| head := 0;
       tail := zeroes |}.

CoFixpoint repeat n : NatStream := 
    {| head := n;
       tail := repeat n|}.

Fixpoint take {A} (n : nat) (s : Stream A) : list A := 
    match n with
    | 0 => nil
    | S m => cons (head s) (take m (tail s))
    end.
Fixpoint nth {A} (n : nat) (s : Stream A) : A := 
    match n with
    | 0 => head s
    | S m => nth m (tail s)
    end.

Eval cbn in take 4 zeroes.

Theorem all_zeroes n : nth n zeroes = 0.
Proof.
    unfold nth.
    induction n.
    compute.
    reflexivity.
    unfold tail.
    unfold zeroes.
    fold zeroes.
    exact IHn.
Qed.

CoInductive StreamEq {A} (a : Stream A) (b : Stream A) := 
    mkStreamEq {eqhead : head a = head b;
                eqtail : StreamEq (tail a) (tail b)}.

Theorem seq_zeroes0 : StreamEq zeroes (repeat 0).
Proof.
    cofix H.
    refine (mkStreamEq _ _ _ _).
    compute. reflexivity.
    compute.  exact H.
    Show Proof.
Defined.

CoFixpoint seq_zeroes1 : StreamEq zeroes (repeat 0) := 
    mkStreamEq zeroes (repeat 0) eq_refl seq_zeroes1.

Axiom stream_eq_ext: forall A (a b : Stream A), StreamEq a b -> a = b.

Theorem eq_zeroes : zeroes = repeat 0.
Proof.
    Print Assumptions zeroes.
    apply stream_eq_ext.
    apply seq_zeroes0.
Qed.

