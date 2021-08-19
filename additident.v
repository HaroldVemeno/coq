(* Define a datatype to represent natural numbers. *)
Inductive nat : Set :=
  (* A natural number can be zero, *)
  | Z : nat
  (* or the successor of another natural number. *)
  | S : nat -> nat.

(* Two is the successor of successor of zero. *)
Definition two : nat := S (S Z).

(* We can find the predecessor. *)
Definition pred (n : nat) : nat :=
  (* Let's investigate the given number: *)
  match n with
    (* If it's zero, let's just return zero. *)
  | Z => Z
    (* Otherwise, pred of "succ of n" is just n. *)
  | S n' => n'
end.

(* We define addition on two "nat"s, recursively.
   A recursive function is defined using Fixpoint. *)
Fixpoint plus (n m : nat) : nat :=
  (* Let's analyze n. *)
  match n with
    (* If it's zero, we return m. *)
  | Z => m
    (* Otherwise, n is S n' for some n'. *)
  | S n' =>
    (* We recursively compute "plus n' m", then apply S. *)
    S (plus n' m)
end.

(* Equality type is defined like this. *)
Inductive eq (A : Set) : A -> A -> Prop :=
  refl : forall x : A, eq A x x.

(* Don't need to understand this now;
   just use equality type as "eq x y" and reflexivity as "refl". *)
Arguments eq {_} x y.
Arguments refl {_ _}.

(* Reflexivity holds by definition. *)
Definition this_is_free : eq (S Z) (S Z) := refl.

(* We can write more complex expressions as "Theorem", and provide "Proof" with tactics. *)
Theorem this_is_almost_free : eq (plus two Z) (plus Z two).
(* If you use Coq IDE locally, you can see "goal" at this point. *)
Proof.
  (* If we evaluate the two sides, they're equal, so we can prove the theorem with "refl". *)
  apply refl.
  (* All goals are satisfied, we close the proof with "Qed".
     Then "this_is_almost_free" is defined with auto-generated body. *)
Qed.

(* Now, we define a utility function "cong":
   if two sides are equal, they're still equal after applying a function on both sides. *)
Theorem cong : forall (f : nat -> nat) (n m : nat), eq n m -> eq (f n) (f m).
Proof.
  (* Bring the parameters as hypotheses. *)
  intros f n m eq_n_m.
  (* The "inversion" tactic can identify how we can satisfy "eq n m" - n and m should be equal. *)
  inversion eq_n_m.
  (* Now n and m are equal, and the goal is "eq (f m) (f m)". How do we close it? *)
  apply refl.
Qed.

(* Let's prove the main theorems. *)
Theorem plus_O_a : forall n : nat, eq (plus Z n) n.
Proof.
  (* Bring the parameters as hypotheses. Hint: See above. *)
  intros.
  (* "plus Z n" is, by definition of plus, "n". *)
  simpl plus.
  apply refl.
Qed.

Theorem plus_a_O : forall n : nat, eq (plus n Z) n.
Proof.
  (* This time, it's not simple at all like the above.
     Let's try induction principle. *)
  induction n as [ | n' IHn ].
    (* Base case : the theorem holds when n = Z (this is trivial.) *)
  - simpl plus.
    apply refl.
    (* Induction case : If the theorem holds with n', the theorem holds with S n'.
       The "If" part is given as hypothesis "IHn" here.
       Let's apply the definition of plus. If you're using IDE, you can see S is extracted out. *)
  - simpl.
    (* The conclusion has S on both sides. Let's strip it. *)
    apply cong.
    (* Now it's exactly the same as the induction hypothesis. *)
    assumption.
Qed.

(* Congratulations! For better introduction, google Coq Software Foundations. *)
