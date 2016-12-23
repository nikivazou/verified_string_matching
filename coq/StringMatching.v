Require Import Arith.
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Program.Wf.
Require Import List.
Require Import PeanoNat.
Require Import Program.
Require Import Wf.

Import ListNotations.

Class Associative {T: Type} (op: T -> T -> T) :=
  {
    associativity: forall x y z, op x (op y z) = op (op x y) z;
  }.

Class Monoid (T: Type) :=
  MkMonoid {
    unit: T;
    op: T -> T -> T;
    monoid_associative: Associative op;
    monoid_left_identity: forall x, op unit x = x;
    monoid_right_identity: forall x, op x unit = x;
  }.

Instance app_Associative: forall T, Associative (@app T).
Proof.
  intro T.
  constructor.
  induction x.
  { reflexivity. }
  { simpl. congruence. }
Defined.

Instance list_Monoid: forall T, Monoid (list T).
Proof.
  intro T.
  apply MkMonoid with (unit := []) (op := @app T).
  { auto with typeclass_instances. }
  { reflexivity. }
  { induction x.
    { reflexivity. }
    { simpl. congruence. }
  }
Defined.

Notation "a ** b" := (op a b) (at level 50).

Class MonoidMorphism
      {Tn Tm: Type}
      `{Mn: Monoid Tn} `{Mm: Monoid Tm}
      (f: Tn -> Tm)
  :=
  {
    morphism_unit: f unit = unit;
    morphism_op: forall x y, f (x ** y) = f x ** f y;
  }.

Class ChunkableMonoid (T: Type) `{Monoid T} :=
  MkChunkableMonoid {
    length: T -> nat;
    drop: nat -> T -> T;
    take: nat -> T -> T;
    drop_spec:
      forall i x,
        i <= length x ->
        length (drop i x) = length x - i;
    take_spec:
      forall i x,
        i <= length x ->
        length (take i x) = i;
    take_drop_spec:
      forall i x, x = take i x ** drop i x;
  }.

Fixpoint list_take {T: Type} i (l: list T) :=
  match i, l with
  | 0, _ => []
  | _, [] => []
  | S i, h::t => h :: list_take i t
  end.

Fixpoint list_drop {T: Type} i (l: list T) :=
  match i, l with
  | 0, _ => l
  | _, [] => []
  | S i, h::t => list_drop i t
  end.

Instance list_ChunkableMonoid: forall T, ChunkableMonoid (list T).
Proof.
  intro T.
  apply MkChunkableMonoid
  with (length := @List.length T) (drop := list_drop) (take := list_take);
    intros.
  { generalize dependent x.
    induction i, x; intros; intuition.
    apply IHi.
    intuition.
  }
  { generalize dependent x.
    induction i, x; intros; intuition.
    simpl in *.
    rewrite IHi; intuition.
  }
  { generalize dependent x.
    induction i, x; intros; intuition.
    simpl in *.
    rewrite <- IHi.
    reflexivity.
  }
Defined.

Program Fixpoint chunk {T: Type} `{M: ChunkableMonoid T}
         (I: { i: nat & i > 0 }) (x: T)
         { measure (length x) }
  : list T :=
  let i := projT1 I in
  match Nat.leb (length x) i with
  | true => [x]
  | false => take i x :: chunk I (drop i x)
  end.
Next Obligation.
  symmetry in Heq_anonymous.
  rewrite Compare_dec.leb_iff_conv in Heq_anonymous.
  rewrite drop_spec.
  { apply Nat.sub_lt.
    { intuition. }
    { intuition. }
  }
  { intuition. }
Defined.

Theorem if_flip_helper {B: Type} {l p: nat}
        (C E: true = (l <=? p) -> B) (D F: false = (l <=? p) -> B):
  (forall (r: true  = (l <=? p)), C r = E r) ->
  (forall (r: false = (l <=? p)), D r = F r) ->
  (if l <=? p as an return an = (l <=? p) -> B then C else D) eq_refl =
  (if l <=? p as an return an = (l <=? p) -> B then E else F) eq_refl.
Proof.
  intros.
  destruct (l <=? p).
  apply H.
  apply H0.
Qed.

Program Fixpoint my_chunk_elim {M: Type} `{ChunkableMonoid M}
        I x { measure (length x) }
  : let i := projT1 I in
    chunk I x =
    match Nat.leb (length x) i with
    | true => [x]
    | false => take i x :: chunk I (drop i x)
    end
  := _.
Next Obligation.
  specialize (my_chunk_elim M H H0).
  unfold chunk.
  unfold chunk_func.
  (*
  match goal with |- context [ Fix_sub ?A_ ?R_ ?Rwf_ ?P_ ?f_ ?x_ ] =>
                  set (x2 := x_);
                  set (f := f_);
                  set (P := P_);
                  set (Rwf := Rwf_);
                  set (R := R_) in *;
                  set (A := A_) in *
  end.
   *)
  rewrite fix_sub_eq.
  {
    simpl.
    destruct (Nat.leb (length x) I) eqn:C; reflexivity.
  }
  {
    intros.
    set (q:=(projT2 (projT2 (projT2 x0)))).
    apply if_flip_helper; intro.
    reflexivity.
    f_equal.
    apply H1.
  }
Qed.

Eval compute in (chunk (existT _ 3 _) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]).
(*
  = [[0; 1; 2]; [3; 4; 5]; [6; 7; 8]; [9]]
  : list (list nat)
 *)

Fixpoint mconcat {M: Type} `{Monoid M} (l: list M): M :=
  match l with
  | [] => unit
  | x::xs => x ** mconcat xs
  end.

Definition strong_induction := well_founded_induction lt_wf.

Theorem morphism_distribution:
  forall {M N: Type}
    `{MM: Monoid M} `{MN: Monoid N}
    `{CMM: @ChunkableMonoid N MN}
    (f: N -> M)
    `{MMf: @MonoidMorphism _ _ MN MM f},
    forall i x,
      f x = mconcat (map f (chunk i x)).
Proof.
  intros.
  remember (length x) as len.
  generalize dependent x.
  induction len using strong_induction; intros.
  rewrite my_chunk_elim.
  simpl.
  destruct i as [i I]; simpl.
  destruct (Nat.leb (length x) i) eqn:LEB.
  {
    simpl.
    now rewrite monoid_right_identity.
  }
  {
    rewrite Compare_dec.leb_iff_conv in LEB.
    simpl.
    rewrite <- H with (y := length (drop i x)).
    {
      rewrite <- morphism_op.
      now rewrite <- take_drop_spec.
    }
    {
      rewrite drop_spec.
      {
        rewrite Heqlen.
        assert (0 < length x) by intuition.
        intuition.
      }
      { intuition. }
    }
    { reflexivity. }
  }
Qed.

Lemma length_list_drop: forall {T: Type} i (x: list T),
  i < Datatypes.length x ->
  Datatypes.length (list_drop i x) = Datatypes.length x - i.
Proof.
  intros.
  generalize dependent i.
  induction x; destruct i; simpl; intros.
  { reflexivity. }
  { reflexivity. }
  { reflexivity. }
  { apply IHx. intuition. }
Qed.

Lemma length_chunk_base:
  forall {T: Type} I (x: list T),
    let i := projT1 I in
    i > 1 ->
    Datatypes.length x <= i ->
    Datatypes.length (chunk I x) = 1.
Proof.
  intros; subst i.
  rewrite my_chunk_elim.
  simpl.
  apply leb_correct in H0.
  rewrite H0.
  reflexivity.
Qed.
Ltac feed H :=
  match type of H with
  | ?foo -> _ =>
    let FOO := fresh in
    assert foo as FOO; [|specialize (H FOO); clear FOO]
  end.

Lemma length_chunk_lt:
  forall {T: Type} I (x: list T),
    let i := projT1 I in
    i > 1 ->
    Datatypes.length x > i ->
    Datatypes.length (chunk I x) < Datatypes.length x.
Proof.
  intros; subst i.
  remember (Datatypes.length x) as len.
  generalize dependent x.
  induction len using strong_induction; intros.
  rewrite my_chunk_elim.
  simpl.
  assert (Datatypes.length x <=? projT1 I = false) as LEB.
  { apply leb_iff_conv. intuition. }
  rewrite LEB.
  simpl.

  remember (list_drop (projT1 I) x) as LD.
  specialize (H1 (Datatypes.length LD)).
  destruct (Datatypes.length LD <=? projT1 I) eqn:LEB2.

  {
    rewrite length_chunk_base.
    { intuition. }
    { intuition. }
    {
      apply leb_complete.
      apply LEB2.
    }
  }

  {

    assert (Datatypes.length LD < len) as A.
    {
      subst LD.
      rewrite length_list_drop.
      { intuition. }
      { intuition. }
    }

    specialize (H1 A).
    feed H1.
    { apply leb_complete_conv in LEB2. intuition. }

    specialize (H1 LD eq_refl).
    intuition.
  }
Qed.

Program Fixpoint pmconcat
        {M: Type}
        `{ChunkableMonoid M}
        I (x: list M) { measure (length x) }: M :=
  let i := projT1 I in
  match ((i <=? 1) || (length x <=? i))%bool with
  | true => mconcat x
  | false => pmconcat I (map mconcat (chunk I x))
  end.
Next Obligation.
  rename Heq_anonymous into COND.
  simpl in COND.
  symmetry in COND.
  rewrite -> Bool.orb_false_iff in COND.
  destruct COND as [A B].
  rewrite Compare_dec.leb_iff_conv in A, B.
  rewrite map_length.
  rewrite my_chunk_elim.
  simpl.
  assert (Datatypes.length x <=? I = false) as D by now apply leb_iff_conv.
  rewrite D.
  simpl.

  assert (I > 1) as L1 by intuition.
  pose proof (@length_chunk_lt M (existT _ I X) (list_drop I x) L1) as LT.
  simpl in *.

  destruct (I <? Datatypes.length (list_drop I x)) eqn:LT1.

  {
    apply Nat.ltb_lt in LT1.
    assert (Datatypes.length (list_drop I x) > I) as GT1 by intuition.
    specialize (LT GT1).
    transitivity (S (Datatypes.length (list_drop I x))).
    { intuition. }
    { rewrite length_list_drop.
      { intuition. }
      { intuition. }
    }
  }

  {
    clear LT L1.
    rewrite length_chunk_base; simpl.
    { intuition. }
    { intuition. }
    { now apply Nat.ltb_ge in LT1. }
  }

Qed.
