Require Import Nat Peano Arith PeanoNat Orders Bool BoolEq Le EqNat.
Open Scope nat_scope.

Fixpoint Mi (b n:nat) : nat := match b with
    | S p => if 100 <? n then n - 10 else Mi p (Mi p (n + 11))
    | 0 => n
end.

Fixpoint M (n: nat) : nat := Mi (n + 100) n.

Eval cbv in M 50.
Eval cbv in M 80.

Theorem M91 : forall n, 90 <= n <= 100 -> M n = 91.
Proof.
    intros.
    destruct H.
    Search le.
    do 10 (
    inversion H0 as [Heq | m Hle];
    vm_compute;
    try reflexivity;
    clear H0 H1 m;
    rename Hle into H0 ).
    do 1 (
    inversion H0 as [Heq | m Hle];
    vm_compute;
    try reflexivity;
    clear H0 H1 m;
    rename Hle into H0 ).
    exfalso.
    apply (le_not_lt _  _ H0).
    unfold "<".
    exact H.
Qed.

Theorem M91 : forall n, n <= 100 -> M n = 91.
Proof.
    intros.
    do 10 (
    inversion H as [Heq | m Hle];
    native_compute;
    try reflexivity;
    clear H H0 m;
    rename Hle into H ).
    do 4 (
    inversion H as [Heq | m Hle];
    native_compute;
    try reflexivity;
    clear H H0 m;
    rename Hle into H ).