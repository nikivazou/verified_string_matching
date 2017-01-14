Require Import String. Open Scope string.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Require Import Tactics. 
Require Import Monoid.

Set Bullet Behavior "Strict Subproofs".


Lemma string_app_assoc : forall x y z : string, x ++ y ++ z = (x ++ y) ++ z.
Admitted. (* Admitted, like in Liquid Haskell *)

Lemma string_app_nil_r : forall s,  s ++ "" = s.
Proof.
  induction s; simpl; eauto.
  rewrite IHs; auto.
Qed.

Instance monoid_list : Monoid string :=
  { ε := "" ;
    mappend := append
  }.
- by apply string_app_assoc.
- simpl; auto.
- by apply string_app_nil_r.
Defined.

Lemma length_drop : 
  forall (i : nat) (x : string),
  i <= String.length x ->
  String.length (substring i (String.length x - i) x) = String.length x - i.
Admitted.

Lemma length_take :
  forall (i : nat) (x : string),
  i <= String.length x -> String.length (substring 0 i x) = i.
Admitted.

Lemma string_take_drop : 
  forall (i : nat) (x : string),
  x = substring 0 i x ◇ substring i (String.length x - i) x.
Admitted.

Instance chunkable_string : ChunkableMonoid string :=
  { length s := String.length s;
    drop n s := substring n (String.length s - n) s;
    take n s := substring 0 n s
  }.
- by apply length_drop. 
- by apply length_take.
- by apply string_take_drop.
Defined.

Definition Symbol := string.

(* External verification is so much easier :) *)
Inductive SM (target : Symbol) :=
| Sm : forall (input : string) (l : list nat),
  SM target.

Definition isGoodIndex (input target : string) (i : nat) :=
  (substring i (length target) input) = target
  /\ i + length target <= length input.
Hint Unfold isGoodIndex.

Definition isGoodIndexDec : forall input target i,
                              {isGoodIndex input target i} + {~ (isGoodIndex input target i)}.
Proof.
  move => input target i.
  destruct (string_dec (substring i (length target) input) target) eqn:Eq.
  - destruct (i + length target <= length input) eqn:Ineq; auto.
    unfold isGoodIndex; right => Contra.
    move: Contra => [_ Contra].
    eauto.
  - unfold isGoodIndex; right => Contra.
    move: Contra => [Contra _].
    eauto.
Qed.

Inductive validSM input target : SM target -> Prop := 
| ValidSM : forall l,
              (List.Forall (isGoodIndex input target) l) ->
              validSM input target (Sm target input l).

Lemma subStrAppendRight : forall (sl sr : string) (i j : nat),
  i + j <= length sl -> substring i j sl = substring i j (sl ◇ sr).
Proof.
  move => sl; induction sl => sr i j HLen.
  - destruct i; destruct j; simpl; try solve [inversion HLen]; auto.
    destruct sr; auto.
  - simpl.
    destruct i; destruct j; simpl; eauto.
    simpl in HLen.
    assert (Hyp : 0 + j <= length sl) by ssromega.
    apply (IHsl sr) in Hyp.
    rewrite Hyp; auto.
Qed. (* Proving some things admitted in Liquid Haskell just to be sure *)
    
Lemma append_length : forall sl sr, length sl <= length (sl ++ sr).
  move => sl; induction sl => sr; simpl; auto.
  eapply leq_ltn_trans; eauto.
Qed.
  
Lemma goodIndexLeft (tg sl sr : string) (i : nat) :
  isGoodIndex sl tg i -> isGoodIndex (sl ◇ sr) tg i.
Proof.  
  unfold isGoodIndex; move => [HSub HLen]; split; simpl.
  - rewrite <- HSub at 2.
    symmetry; apply subStrAppendRight; auto.
  - eapply leq_trans; eauto.
    apply append_length.
Qed.
  
(* Changed recursion to decrementing hi, so that it is structurally recursive *)
Fixpoint makeIndicesAux (s tg : string) (lo cnt : nat) : list nat :=
  match cnt with
    | O => nil 
    | S cnt' => let rest := makeIndicesAux s tg lo cnt' in
                if isGoodIndexDec s tg (lo + cnt) then (lo + cnt)::rest else rest
  end.

Lemma makeIndicesAux_correct : 
  forall cnt s tg lo,
    List.Forall (isGoodIndex s tg) (makeIndicesAux s tg lo cnt).
Proof.
  move => cnt; induction cnt => s tg lo.
  - simpl; destruct (isGoodIndexDec s tg lo) eqn:Good; simpl; auto.
  - simpl; destruct (isGoodIndexDec s tg (lo + cnt.+1)) eqn:Good; simpl; auto.
Qed.    

Definition makeIndices (s tg : string) (lo hi : nat) : list nat :=
  makeIndicesAux s tg lo (hi - lo).

(* Discrepancy (length sl == 0) because of using nats instead of ints *)
Definition makeNewIndices (sl sr tg : string) : list nat :=
  if (length tg < 2) then nil
  else makeIndices (sl ◇ sr) tg (length sl - (length tg - 1)) (length sl - 1).

Lemma makeNewIndices_correct : forall sl sr tg,  
  List.Forall (isGoodIndex (sl ◇ sr) tg) (makeNewIndices sl sr tg).
Proof.
  move => sl sr tg.
  unfold makeNewIndices, makeIndices.
  destruct (length tg < 2); auto.
  apply makeIndicesAux_correct; auto.
Qed.

Definition shiftStringRight (target sl sr : string) (i : nat) : nat :=
  i + length sl.

Lemma substring_append_left :
  forall (sl sr : string) (i j : nat), 
  substring i j sr = substring (i + length sl) j (sl ◇ sr).
Admitted. (* Just like in liquid Haskell *)
    
Lemma append_length_2 : 
  forall sl sr, String.length sl + String.length sr = String.length (sl ++ sr).
Proof.
  induction sl => sr; simpl; auto.
  rewrite <- IHsl; auto.
Qed.
  
Lemma shiftStringRightCorrect : 
  forall tg sl sr i, isGoodIndex sr tg i -> 
                     isGoodIndex (sl ◇ sr) tg (i + length sl).
Proof.
  unfold isGoodIndex; move => tg sl sr i [HSub HLen]; split; simpl; auto.
  - rewrite <- HSub at 2.
    symmetry. apply substring_append_left; auto.
  - rewrite -append_length_2. simpl in *.
    ssromega.
Qed.

Lemma mapShiftZero : forall l target input,
 [seq shiftStringRight target "" input i | i <- l] = l.
Proof.
  induction l => target input; simpl in *; eauto.
  rewrite IHl.
  unfold shiftStringRight; simpl; auto.
  rewrite addn0; auto.
Qed.

Lemma newIsNullLeft : forall s t,  makeNewIndices "" s t = nil.
  move => s t; unfold makeNewIndices; simpl; auto.
  destruct (String.length t < 2); auto.
Qed.

Lemma makeNewIndicesNullSmallInput (s t : string) (lo hi : nat) :
  1 + String.length s <= String.length t ->
  makeIndices s t lo hi = nil.
Proof.
  move => Rel.
  unfold makeIndices.
  remember (hi - lo) as cnt.
  move : lo hi Heqcnt s t Rel.
  induction cnt => lo hi HCnt s t Rel; auto.
  simpl.
  destruct (isGoodIndexDec s t (lo + cnt.+1)) eqn:Good; simpl; auto.
  - unfold isGoodIndex in i.
    inversion i; exfalso.
    clear H Good i.
    simpl in H0. ssromega.
  - eapply (IHcnt _ (hi -1)); eauto.
    ssromega.
Qed.

Lemma makeNewIndicesSmallIndex (s t : string) (lo hi : nat) :
  String.length t < 2 + String.length s ->
  String.length s - (String.length t - 1) <= lo ->
  lo <= hi ->
  makeIndices s t lo hi = nil.
Proof.
  unfold makeIndices.
  remember (hi - lo) as cnt.
  move: lo hi s t Heqcnt.
  induction cnt => lo hi s t Heqcnt Len1 Len2 Rel; simpl; auto.
  destruct (isGoodIndexDec s t (lo + cnt.+1)) eqn:Good; simpl; auto.
  - exfalso.
    unfold isGoodIndex in i; inversion i.
    clear H Good i.
    simpl in H0.
    ssromega.
  - eapply (IHcnt _ (hi-1)); eauto; try ssromega.
Qed.

Lemma newIsNullRight : forall s t, makeNewIndices s "" t = nil.
  move => s t.
  unfold makeNewIndices; simpl; rewrite string_app_nil_r; simpl.
  destruct (String.length t < 2) eqn:LenT; auto.
  destruct (1 + String.length s <= String.length t) eqn:Rel; auto.
  - apply makeNewIndicesNullSmallInput; auto.
  - apply makeNewIndicesSmallIndex; auto; try ssromega.
Qed.
  
Instance monoid_SM (target : Symbol) : Monoid (SM target) :=
  {
    ε := Sm target "" nil;
    mappend sm1 sm2 :=
      let '(Sm x xis) := sm1 in
      let '(Sm y yis) := sm2 in 
      let xis' := xis in 
      let xyis := makeNewIndices x y target in
      let yis' := map (shiftStringRight target x y) yis in
      Sm target (x ◇ y) (List.app xis' (List.app xyis yis'))
  }.
- simpl.
  move => x y z; destruct x; destruct y; destruct z; simpl; auto.
  admit.
- simpl.
  move => x. destruct x eqn:X; simpl.
  rewrite (mapShiftZero l target input). 
  rewrite newIsNullLeft; simpl; auto.
- simpl. move => x; destruct x eqn:X ; simpl.
  rewrite string_app_nil_r.
  rewrite newIsNullRight.
  simpl; auto; rewrite List.app_nil_r; simpl; auto.
Admitted.
  