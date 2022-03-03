Inductive formula : Set :=
| atom : nat -> formula
| false_f : formula
| or_f : formula -> formula -> formula
| and_f : formula -> formula -> formula
| implies_f : formula -> formula -> formula.

Infix "/\f" := and_f (at level 60, right associativity).
Infix "\/f" := or_f (at level 65, right associativity).
Infix "->f" := implies_f (at level 70, right associativity).

(* Some variable constants for convenience *)
Notation X := (atom 0).
Notation Y := (atom 1).
Notation Z := (atom 2).

Inductive MID := bot | mid | top.

Definition sel {A} (m : MID) (x y z : A): A :=
  match m with
  | bot => x
  | mid => y
  | top => z
  end.

Definition meet (m n : MID): MID :=
  sel m (sel n bot bot bot)
        (sel n bot mid mid)
        (sel n bot mid top).

Definition join (m n : MID): MID :=
  sel m (sel n bot mid top)
        (sel n mid mid top)
        (sel n top top top).

Definition impl (m n : MID): MID :=
  sel m (sel n top top top)
        (sel n bot top top)
        (sel n bot mid top).

Definition map := nat -> MID.

Fixpoint valuation (c : formula) (m : map) : MID :=
  match c with
  | atom v => m v
  | false_f => bot
  | a \/f b => join (valuation a m) (valuation b m)
  | a /\f b => meet (valuation a m) (valuation b m)
  | a ->f b => impl (valuation a m) (valuation b m)
  end.

Definition MID_valid (c : formula) := forall m, valuation c m = top.

Definition substitution := nat -> formula.

Fixpoint subst (c : formula) (s : substitution) : formula :=
  match c with
  | atom v => s v
  | false_f => false_f
  | a \/f b => subst a s \/f subst b s
  | a /\f b => subst a s /\f subst b s
  | a ->f b => subst a s ->f subst b s
  end.

Inductive hilbert : formula -> Prop :=
| app_h : forall a b, hilbert (a ->f b) -> hilbert a -> hilbert b
| subst_h : forall a s, hilbert a -> hilbert (subst a s)
| k_h : hilbert (X ->f Y ->f X)
| s_h : hilbert ((X ->f Y ->f Z) ->f (X ->f Y) ->f (X ->f Z))
| fst_h : hilbert (X /\f Y ->f X)
| snd_h : hilbert (X /\f Y ->f Y)
| pair_h : hilbert (X ->f Y ->f X /\f Y)
| inl_h : hilbert (X ->f X \/f Y)
| inr_h : hilbert (Y ->f X \/f Y)
| either_h : hilbert ((X ->f Z) ->f (Y ->f Z) ->f (X \/f Y ->f Z))
| absurd_h : hilbert (false_f ->f X).

Definition LEM := X \/f (X ->f false_f).

Lemma hilbert_MID_sound : forall c, hilbert c -> MID_valid c.
Proof with (try easy).
  fix HH 1.
  intros.
  unfold MID_valid.
  induction H; intros.
  destruct a, b...
  all: simpl in *.
  all: multimatch goal with
  | H: forall m : map, _, H2: forall m : map, _ |- _ => pose proof (H m); pose proof (H2 m)
  | H: forall m : map, _ |- _ => pose proof (H m)
  | _ => idtac
  end; try easy.
  destruct (m n), (m n0)...
  destruct (m n)...
  all: multimatch goal with
  | |- join ?U ?I = top => destruct (join U I)
  | |- meet ?U ?I = top => destruct (meet U I)
  | _ => idtac
  end; try easy.
  all: multimatch goal with
  | [ u : nat |- _ ] => destruct (m u)
  | [ |- impl (valuation ?b1 ?m) (valuation ?b2 ?m) = top ] => destruct (impl (valuation b1 m) (valuation b2 m))
  | _ => idtac
  end; try easy.
  all: multimatch goal with
  | [ |- impl (valuation ?b1 ?m) (valuation ?b2 ?m) = top ] => destruct (impl (valuation b1 m) (valuation b2 m))
  | [ u : nat |- _ ] => destruct (m u)
  | _ => idtac
  end; try easy.
  all: multimatch goal with
  | H: join ?U ?I = top |- _ => destruct (join U I)
  | H: meet ?U ?I = top |- _ => destruct (meet U I)
  | [H: impl (valuation ?b1 ?m) (valuation ?b2 ?m) = top |- _ ] => destruct (impl (valuation b1 m) (valuation b2 m))
  | _ => idtac
  end; try easy.
  all: multimatch goal with
  | |- context [?m 2] => destruct (m 2)
  | _ => idtac
  end; try easy.
  all: multimatch goal with
  | |- context [?m 1] => destruct (m 1)
  | _ => idtac
  end; try easy.
  all: multimatch goal with
  | |- context [?m 0] => destruct (m 0)
  | _ => idtac
  end; try easy.

  pose (mbot (n : nat) := valuation (s n) m).
  pose proof (IHhilbert mbot).
  clear -H1.
  induction a; intros; try easy; simpl in *.
  assert (valuation a1 mbot = top \/ valuation a2 mbot = top).
  destruct (valuation a1 mbot), (valuation a2 mbot); try auto.
  destruct H.
  rewrite (IHa1 ltac:(easy)).
  destruct (valuation (subst a2 s) m); try easy.
  rewrite (IHa2 ltac:(easy)).
  destruct (valuation (subst a1 s) m); try easy.
  destruct (valuation a1 mbot), (valuation a2 mbot); try easy.
  rewrite (IHa1 eq_refl).
  rewrite (IHa2 eq_refl).
  reflexivity.


Lemma LEM_not_MID_valid : ~ MID_valid LEM.
Proof.
  intros H.
  unfold MID_valid, LEM in H.
  specialize (H (fun n => mid)).
  simpl in H.
  easy.
Qed.


Theorem hilbert_LEM_not_provable : ~ hilbert LEM.
Proof.
  (* This should not need modifying *)
  auto using LEM_not_MID_valid, hilbert_MID_sound.
Qed.
