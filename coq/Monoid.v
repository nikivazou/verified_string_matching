Require Import String. Open Scope string.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Require Import Tactics. 

Set Bullet Behavior "Strict Subproofs".

Class Monoid (T: Type) :=
  MkMonoid {
    ε : T;
    mappend  : T -> T -> T;
    mAssoc   : forall x y z, mappend x (mappend y z) = mappend (mappend x y) z;
    mIdLeft  : forall x, mappend ε x = x;
    mIdRight : forall x, mappend x ε = x;
}.

Notation "x ◇ y" := (mappend x y) (at level 50).

(* Example monoid (lists) *)
Instance monoid_list : forall {A}, Monoid (list A) :=
  { ε := nil ;
    mappend := @seq.cat A
  }.
Proof.
  - (* assoc *)
    by apply List.app_assoc.
  - (* id-left *)
    by apply List.app_nil_l.
  - (* id-right *)
    by apply List.app_nil_r.
Defined.

Class MonoidMorphism {Tn Tm: Type} `{Mn: Monoid Tn} `{Mm: Monoid Tm}
      (f: Tn -> Tm) :=
  {
    morphism_mempty  : f ε = ε;
    morphism_mappend : forall x y, f (x ◇ y) = f x ◇ f y
  }.

Class ChunkableMonoid (T: Type) `{Monoid T} :=
  MkChunkableMonoid {
    length : T -> nat;
    drop   : nat -> T -> T;
    take   : nat -> T -> T;
    drop_spec:
      forall i x,
        i <= length x ->
        length (drop i x) = length x - i;
    take_spec:
      forall i x,
        i <= length x ->
        length (take i x) = i;
    take_drop_spec:
      forall i x, x = take i x ◇ drop i x;
  }.

(* Example Chunkable: List *)
Instance chunkableMonoid_list : forall {A}, ChunkableMonoid (list A) :=
  { length := @seq.size A;
    drop   := @seq.drop A;
    take   := @seq.take A
  }.
Proof.
  - (* drop-spec *)
    intros; by apply seq.size_drop.
  - (* take-spec *)
    move => i x HSize.
    rewrite seq.size_take.
    destruct (i < size x) eqn:Size; auto. ssromega.
  - (* take-drop *)
    intros; symmetry; by apply seq.cat_take_drop.
Defined.

(* Helper induction principle for Chunkables *)
Definition lt_len {A} `{_ : ChunkableMonoid A} (x y : A) := 
  length x < length y.

Require Import Coq.Program.Wf.
Require Import Coq.Arith.Wf_nat.

Theorem lt_len_wf {A} `{M1 : Monoid A} `{M2 : @ChunkableMonoid _ M1} : 
  well_founded (@lt_len A M1 M2).
Proof.
  eapply (well_founded_lt_compat _ length).
  move => x y HLen.
  unfold lt_len in *.
  ssromega.
Qed.

(* Approach 1: Fuel. Go extrinsic as much as possible *)
Fixpoint chunk {A: Type} `{M: ChunkableMonoid A}
        (fuel : nat) (i : nat) (x : A) : option (list A) :=
  match fuel with
    | O => None
    | S fuel' =>
      if length x <= i then Some (cons x nil)
      else match chunk fuel' i (drop i x) with
        | Some res => Some (cons (take i x) res)
        | None => None
      end                                 
  end.

Definition chunk_res {A} `{_ : ChunkableMonoid A}
           (i : nat) (x : A) (v : list A) : Prop :=
  if length x <= i then length v = 1
  else if i == 1 then length v = length x
  else length v < length x.

(* Fuel lemmas - monotonicity 1 *)
Lemma chunk_fuel_lt : 
  forall {A} `{_ : ChunkableMonoid A} n2 n1 i (x : A),
    n1 < n2 -> 
    chunk n1 i x = chunk n2 i x \/ chunk n1 i x = None.
Proof.
  move => A ? ? n2.
  induction n2 => n1 i x HN12.
  - inversion HN12.
  - unfold chunk.
    destruct n1 eqn:HN1; simpl; auto.
    destruct (length x <= i) eqn:LenX; auto.
    fold chunk.
    destruct (IHn2 n i (drop i x)); auto.
    * destruct (chunk n i (drop i x)); subst; auto;
      destruct (chunk n2 i (drop i x)); subst; auto;
      inversion H; auto.
    * right; rewrite H; auto.
Qed.

(* Sufficient condition for result *)
Lemma chunk_fuel_length_sufficient :
  forall {A} `{_ : ChunkableMonoid A} n i (x : A),
    i > 0 -> length x < n ->
    exists x', chunk n i x = Some x'.
Proof.
  move => A ? ? n.
  induction n=> i x HI HLen.
  - inversion HLen.
  - destruct (chunk n.+1 i x) eqn:Chunk; eauto.
    exfalso.
    unfold chunk in Chunk.
    destruct (length x <= i) eqn:LenX; auto.
    + inversion Chunk.
    + fold chunk in Chunk.
      destruct (IHn i (drop i x)) as [x' Hx']; auto.
      * rewrite drop_spec; ssromega.
      * rewrite Hx' in Chunk; subst; auto.
        inversion Chunk.
Qed.

(* Actual monotonicity *)
Lemma chunk_fuel_monotonic :
  forall {A} `{_ : ChunkableMonoid A} n2 n1 i (x : A),
    i > 0 -> n1 < n2 -> length x < n1 ->
    chunk n1 i x = chunk n2 i x.
Proof.
  intros.
  destruct (chunk_fuel_length_sufficient n1 i x) as [x' Hx']; auto.
  destruct (chunk_fuel_lt n2 n1 i x) as [Hyp1 | Hyp2]; auto.
  rewrite Hyp2 in Hx'; congruence.
Qed.

(* Also works with le *)
Lemma chunk_fuel_monotonic' :
  forall {A} `{_ : ChunkableMonoid A} n2 n1 i (x : A),
    i > 0 -> n1 <= n2 -> length x < n1 ->
    chunk n1 i x = chunk n2 i x.
Proof.
  intros.
  destruct (n1 == n2) eqn:Heq.
  - assert (n1 = n2) by ssromega. subst. auto.
  - assert (n1 < n2) by ssromega. apply chunk_fuel_monotonic; auto.
Qed.

(* Specification of chunk - existential version *)
Theorem chunk_spec : forall {A} i (x : A) `{_ : ChunkableMonoid A},
   i > 0 -> 
   exists l, chunk (length x).+1 i x = Some l /\ chunk_res i x l.
Proof.
  move => A i x ? ? HI.
  unfold chunk_res.
  destruct (length x <= i) eqn:LenX.
  - exists (cons x nil); split; auto.
    unfold chunk. rewrite LenX; auto.
  - destruct (i==1) eqn:HI1.
    + (* Case i == 1 *)
      assert (i = 1) by ssromega. subst; clear HI1.
      induction x using (well_founded_induction lt_len_wf).
      destruct (length x <= 1) eqn:Len; try congruence.
      remember (length (drop 1 x)) as n.
      assert (HDrop: length x = n.+1)
          by (rewrite Heqn drop_spec; eauto; ssromega).
      unfold chunk.
      destruct (n == 1) eqn:HN.
      * (* Special case when n = 1 *)
        assert (HN1: n = 1) by ssromega.
        rewrite HDrop.
        rewrite !HN1; subst; simpl; rewrite !HN1; simpl; auto.
        exists [:: take 1 x ; drop 1 x]; auto.
      * fold chunk.
        rewrite Len.
        specialize (H (drop 1 x)).
        destruct H as [l' [HC HL]]; try solve [unfold lt_len; ssromega].
        subst; rewrite HDrop.
        rewrite HC.
        exists (take 1 x :: l'); split; auto.
        rewrite -HL; simpl; auto.
    + (* General case *)
      induction x using (well_founded_induction lt_len_wf).
      unfold chunk.
      rewrite LenX; simpl.
      specialize (H (drop i x)).
      destruct (length (drop i x) <= i) eqn:HDI; auto.
      * unfold chunk.
        destruct (length x); auto; try ssromega.
        fold chunk.
        rewrite HDI.
        exists [:: take i x ; drop i x]; split; auto.
        simpl; ssromega.
      * destruct H as [l' [HC HL]]; 
        try solve [unfold lt_len; rewrite drop_spec; ssromega]; auto.
        fold chunk.
        assert ((length (drop i x)).+1 < length x)
          by (rewrite drop_spec; auto; ssromega).
        rewrite <- (chunk_fuel_monotonic _ _ i (drop i x) HI H); auto.
        rewrite HC.
        exists (take i x :: l'); simpl; split; auto.
        simpl in HL.
        ssromega.
Qed.

(* Non-existential version of chunk_spec *)
Corollary chunk_spec' : forall {A} i (x : A) `{_ : ChunkableMonoid A} l,
   i > 0 -> 
   chunk (length x).+1 i x = Some l -> chunk_res i x l.
Proof.
  move => A i x M CM l HI HC.
  move: (@chunk_spec A i x M CM HI) => [l' [H1 ? ]].
  rewrite HC in H1.
  inversion H1; subst; auto.
Qed.

Corollary chunk_res_not_none :
  forall {A} i (x : A) `{_ : ChunkableMonoid A},
    i > 0 -> chunk (length x).+1 i x = None -> False.
Proof.
  move => A i x M CM HI HC.
  move: (@chunk_spec A i x M CM HI) => [l [HC' _]].
  congruence.
Qed.

(* Playing with non-option version. Not easy to reason about *)
Definition chunk' {A : Type} `{M : ChunkableMonoid A} 
        (i : nat) (x : A) (HI : i > 0) : list A.
  destruct (chunk (length x).+1 i x) eqn:HC.
  - exact l.
  - exfalso. 
    eapply chunk_res_not_none; eauto.
Defined.
Hint Unfold chunk'.

Fixpoint mconcat {M: Type} `{Monoid M} (l: list M): M :=
  match l with
  | nil => ε
  | x::xs => x ◇ mconcat xs
  end.

Theorem morphism_distribution:
  forall {M N: Type} `{MM: Monoid M} `{MN: Monoid N}
        `{CMM: @ChunkableMonoid N MN} 
        (f : N -> M) `{MMf: @MonoidMorphism _ _ MN MM f}
        i (HI : i > 0) x,
    exists l, chunk (length x).+1 i x = Some l /\ f x = mconcat (map f l).
Proof.
  move => M N ? ? ? f HF i HI x.
  induction x using (well_founded_induction lt_len_wf).
  pose proof (chunk_spec i x HI) as Hyp.
  move: Hyp => [l [HC HRes]].
  exists l; split; auto.
  unfold chunk in HC.
  destruct (length x <= i) eqn:Len.
  - inversion HC; subst; simpl; auto.
    rewrite mIdRight; auto.
  - fold chunk in HC.
    assert (HLT: (length (drop i x)).+1 <= length x)
      by (rewrite drop_spec; ssromega).
    rewrite <- (chunk_fuel_monotonic' _ _ i (drop i x) HI HLT) in HC; auto.
    specialize (H (drop i x)).
    destruct H as [l' [HC' HL']]; auto.
    rewrite HC' in HC.
    inversion HC; subst; simpl; auto.
    rewrite -HL' -morphism_mappend -take_drop_spec.
    reflexivity.
Qed.

Corollary morphism_distribution'
   {M N: Type} `{MM: Monoid M} `{MN: Monoid N}
        `{CMM: @ChunkableMonoid N MN} 
        (f : N -> M) `{MMf: @MonoidMorphism _ _ MN MM f}
        i (HI : i > 0) x l :
    chunk (length x).+1 i x = Some l -> f x = mconcat (map f l).
Proof.
  move => HC.
  destruct (morphism_distribution f i HI x) as [l' [HC' HL']].
  rewrite HC in HC'; inversion HC'; subst; auto.
Qed.
  
(* Axiomatize paralelism *)
Axiom Strategy : Type.
Axiom parStrategy : Strategy.
Axiom withStrategy : forall {A},  Strategy -> A -> A.
Axiom withStrategy_spec : forall {A} (s : Strategy) (x : A), 
                            withStrategy s x = x.

Definition pmap {A B} (f : A -> B) (xs : seq A) := 
  withStrategy parStrategy (seq.map f xs).

Lemma pmap_map : forall {A B} (f : A -> B) (xs : seq A),
    pmap f xs = map f xs.
Proof.
  intros. unfold pmap. rewrite withStrategy_spec. reflexivity.
Qed.

Section PMConcat.


(* Similar treatment of PM Concat with Fuel *)
(* Maybe there could be some automation here, since they are extremely similar *)
Fixpoint pmconcat {A} `{_ : ChunkableMonoid A} 
         (fuel : nat) i (xs : seq A) : option A :=
  match fuel with
    | O => None
    | S fuel' =>
      if (i <= 1) || (length xs <= 1) then Some (mconcat xs)
      else match chunk (length xs).+1 i xs with
             | Some l => pmconcat fuel' i (pmap mconcat l)
             | None => None
           end
  end.

Lemma pmconcat_fuel_lt : 
  forall {A} `{_ : ChunkableMonoid A} n2 n1 i (xs : seq A),
    n1 < n2 -> 
    pmconcat n1 i xs = pmconcat n2 i xs \/ pmconcat n1 i xs = None.
Proof.
  move => A ? ? n2.
  induction n2 => n1 i xs HN12.
  - inversion HN12.
  - unfold pmconcat.
    destruct n1 eqn:HN1; auto.
    destruct (i <= 1) eqn:HI1; auto.
    destruct (length xs <= 1) eqn:LenX; auto.
    destruct (false || false); auto. (* Avoiding simpl :) *)
    assert (HI : 0 < i) by ssromega.
    pose proof (chunk_spec i xs HI) as Hyp.
    move: Hyp => [l [HC HL]].
    rewrite HC.
    fold pmconcat.
    eapply IHn2; eauto.
Qed.

Lemma pmconcat_fuel_length_sufficient :
  forall {A} `{_ : ChunkableMonoid A} n i (xs : seq A),
    length xs < n ->
    exists xs', pmconcat n i xs = Some xs'.
Proof.
  move => A ? ? n.
  induction n=> i xs HLen.
  - inversion HLen.
  - destruct (pmconcat n.+1 i xs) eqn:PM; eauto.
    exfalso.
    unfold pmconcat in PM.
    destruct (i <= 1) eqn:HI1; try solve [simpl in *; congruence].
    destruct (length xs <= 1) eqn:LenX; try solve [simpl in *; congruence].
    destruct (false || false) in PM; try congruence.
    fold pmconcat in PM.
    pose proof (chunk_spec i xs) as Hyp.
    destruct Hyp as [l [HC HL]]; try ssromega.
    rewrite HC in PM.
    destruct (IHn i (pmap mconcat l)) as [xs' Hxs']; auto.
    + unfold chunk_res in HL.
      destruct (length xs <= i) eqn:Len; auto.
      * rewrite pmap_map. simpl in *. rewrite size_map.
        rewrite HL. ssromega.
      * destruct (i==1) eqn:I; try ssromega.
        rewrite pmap_map. simpl in *.
        rewrite size_map. subst. ssromega.
    + congruence.
Qed.
  
Lemma pmconcat_fuel_monotonic :
  forall {A} `{_ : ChunkableMonoid A} n2 n1 i (xs : seq A),
    n1 < n2 -> length xs < n1 ->
    pmconcat n1 i xs = pmconcat n2 i xs.
Proof.
  intros.
  destruct (pmconcat_fuel_length_sufficient n1 i xs) as [xs' Hxs']; auto.
  destruct (pmconcat_fuel_lt n2 n1 i xs) as [Hyp1 | Hyp2]; auto.
  rewrite Hyp2 in Hxs'; congruence.
Qed.

Lemma pmconcat_fuel_monotonic' :
  forall {A} `{_ : ChunkableMonoid A} n2 n1 i (xs : seq A),
    n1 <= n2 -> length xs < n1 ->
    pmconcat n1 i xs = pmconcat n2 i xs.
Proof.
  intros.
  destruct (n1 == n2) eqn:Heq.
  - assert (n1 = n2) by ssromega. subst. auto.
  - assert (n1 < n2) by ssromega. apply pmconcat_fuel_monotonic; auto.
Qed.

Corollary pmconcat_len_spec : 
  forall {A} `{ChunkableMonoid A} i (xs : seq A), 
    exists l, pmconcat (length xs).+1 i xs = Some l.
Proof.
  intros; eapply pmconcat_fuel_length_sufficient; eauto.
Qed.

End PMConcat.

Lemma mconcat_split {A} `{_ : ChunkableMonoid A} (xs : seq A):
  forall (i : nat), i <= length xs -> 
  mconcat xs = mconcat (seq.take i xs) ◇ mconcat (seq.drop i xs).
Proof.
  induction xs => i HLen; simpl.
  - rewrite mIdLeft; reflexivity.
  - destruct i; simpl; auto.
    + rewrite mIdLeft; auto.
    + rewrite -mAssoc.
      rewrite -IHxs; auto.
Qed.

Lemma mconcat_chunk {A} `{_ : ChunkableMonoid A} (xs : seq A) :
  forall (i : nat), i > 0 ->
    exists l, chunk (length xs).+1 i xs = Some l /\ 
              mconcat xs = mconcat (map mconcat l).
Proof.
  move => i HI.
  induction xs using (well_founded_induction lt_len_wf).
  pose proof (chunk_spec i x HI) as Hyp.
  move : Hyp => [l [HC HL]].
  rewrite HC.
  exists l; split; auto.
  unfold chunk in HC.
  fold chunk. (* This should do the following rewrite, but whatever *)
  (* I don't know what the hell went wrong here *)
  assert (WTF: (fix
            chunk (A : Type) (H : Monoid A) (M : ChunkableMonoid A)
                  (fuel i : nat) (x : A) {struct fuel} : 
            option (seq A) :=
              match fuel with
              | 0 => None
              | fuel'.+1 =>
                  if length x <= i
                  then Some [:: x]
                  else
                   match chunk A H M fuel' i (drop i x) with
                   | Some res => Some (take i x :: res)
                   | None => None
                   end
              end) (seq A) monoid_list chunkableMonoid_list = chunk)
  by auto.
  rewrite WTF in HC; clear WTF.
  destruct (length x <= i) eqn:LenX; auto.
  - inversion HC; simpl in *; subst; simpl; auto.
    rewrite mIdRight; auto.
  - destruct (chunk (length x) i (drop i x)) eqn:HC'; try congruence.
    inversion HC; subst; auto.
    assert (HIX: i <= length x)
      by (destruct (i <= length x) eqn:HIX; try ssromega; auto).
    specialize (H1 (drop i x)).
    assert (HI' : length x - i < length x)
      by (apply /ltP; apply PeanoNat.Nat.sub_lt; try ssromega;
          apply /leP; auto).
    destruct H1 as [l' [HCD HL']].
    + unfold lt_len.
      rewrite drop_spec; auto.
    + pose proof (chunk_fuel_monotonic' (length x)
                                        (length (drop i x)).+1)
           i (drop i x) HI as Hyp.
      rewrite -Hyp in HC'; auto; clear Hyp.
      * rewrite HC' in HCD.
        inversion HCD; subst; simpl; auto.
        rewrite -HL'. apply mconcat_split; auto.
      * rewrite drop_spec; auto.
Qed.

Theorem pmconcat_equivalence {A} `{_ : ChunkableMonoid A} i (xs : seq A) :
  exists l, pmconcat (length xs).+1 i xs = Some l /\ l = mconcat xs.
Proof. 
  pose proof (pmconcat_len_spec i xs) as Hyp.
  move: Hyp => [l HL].
  exists l; split; auto.
  induction xs using (well_founded_induction lt_len_wf).
  unfold pmconcat in HL.
  destruct (i<=1) eqn:HI1; 
    try solve [simpl in HL; inversion HL; auto].
  destruct (length x <= 1) eqn:XS1; 
    try solve [simpl in HL; inversion HL; auto].
  destruct (false || false); try congruence.
  destruct (chunk (length x).+1 i x) eqn:HC; try congruence.
  fold pmconcat in HL.
  
  destruct (mconcat_chunk x i) as [l1 [HC' HL']]; try ssromega.
  rewrite HC in HC'. inversion HC'; subst.
  rewrite HL'.
  
  specialize (H1 (pmap mconcat l1)).
  rewrite pmap_map in H1.

  assert (Lens: (length [seq mconcat i | i <- l1]).+1 <= length x).
  { 
    simpl.
    rewrite size_map.
    apply chunk_spec' in HC; try ssromega.
    unfold chunk_res in HC.
    destruct (length x <= i) eqn:Len; simpl in *; try ssromega.
    destruct (i == 1) eqn:I1; simpl in *; try ssromega.
  }

  rewrite -H1; auto.
  rewrite pmap_map in HL.
  
  pose proof (pmconcat_fuel_monotonic' (length x) 
                                      ((length [seq mconcat i | i <- l1]).+1)
                                      i [seq mconcat i | i <- l1]) as Hyp.
  rewrite -Hyp in HL; auto.
Qed.  

Theorem parallelization_correct {N M} (f : N -> M) 
        `{MN : Monoid N} `{MM : Monoid M}
        `{CN : @ChunkableMonoid N MN} `{CM : @ChunkableMonoid M MM}
        `{Mf : @MonoidMorphism N M MN MM f} (x : N) (i j : nat):
  i > 0 -> j > 0 -> 
  exists l, chunk (length x).+1 j x = Some l /\ 
            Some (f x) = pmconcat (length (pmap f l)).+1 i (pmap f l).
Proof.
  move => HI HJ.
  destruct (chunk_spec j x HJ) as [l [HC HL]].
  exists l; split; auto.
  destruct (pmconcat_equivalence i (pmap f l)) as [l' [HP HL']].
  rewrite HP.
  rewrite pmap_map in HL'.
  rewrite HL'.
  destruct (@morphism_distribution M N MM MN CN f Mf j HJ x)
    as [x' [HC' H2]].
  rewrite HC in HC'; inversion HC'; subst; auto.
  rewrite -H2 in HP.
  rewrite H2.
  auto.
Qed.

(* Final theorem :) *)
Corollary parallelization_correct' {N M} (f : N -> M) 
        `{MN : Monoid N} `{MM : Monoid M}
        `{CN : @ChunkableMonoid N MN} `{CM : @ChunkableMonoid M MM}
        `{Mf : @MonoidMorphism N M MN MM f} (x : N) (i j : nat) l:
  i > 0 -> j > 0 -> 
  chunk (length x).+1 j x = Some l ->
  Some (f x) = pmconcat (length (pmap f l)).+1 i (pmap f l).
Proof.
  move => HI HJ HC.
  destruct (parallelization_correct f x i j HI HJ)
    as [l' [HC' HL']].
  rewrite HC in HC'; inversion HC'; subst; auto.
Qed.