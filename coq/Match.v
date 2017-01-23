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

Definition isGoodIndex (input tg : string) (i : nat) :=
  (substring i (length tg) input) = tg
  /\ i + length tg <= length input.
Hint Unfold isGoodIndex.

Definition isGoodIndexDec : forall input tg i,
                              {isGoodIndex input tg i} + {~ (isGoodIndex input tg i)}.
Proof.
  move => input tg i.
  destruct (string_dec (substring i (length tg) input) tg) eqn:Eq.
  - destruct (i + length tg <= length input) eqn:Ineq; auto.
    unfold isGoodIndex; right => Contra.
    move: Contra => [_ Contra].
    eauto.
  - unfold isGoodIndex; right => Contra.
    move: Contra => [Contra _].
    eauto.
Qed.

(* External verification is so much easier :) *)
Inductive SM (tg : Symbol) :=
| Sm : forall (input : string) (l : list nat), SM tg.

Inductive validSM tg : SM tg -> Prop := 
| ValidSM : forall input l,
              (List.Forall (isGoodIndex input tg) l) ->
              validSM tg (Sm tg input l).
(* TODO: Add
         List.Forall (isGoodIndex input tg) l ->
         SM tg. *)

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

Lemma subStrConcatBack1 input input' j i :    
  i + j <= length input ->
  substring i j input = substring i j (input ◇ input').
Admitted. (* As in liquid Haskell *)

Lemma subStrConcatBack2 input input' j i : 
  i + j <= length input -> 
  length input <= length (input ◇ input').
Admitted. (* As in liquid Haskell *)

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
    | S cnt' => 
      let rest := makeIndicesAux s tg lo.+1 cnt' in
      if isGoodIndexDec s tg lo then lo::rest else rest
  end.

Lemma makeIndicesAux_correct : 
  forall cnt s tg lo,
    List.Forall (isGoodIndex s tg) (makeIndicesAux s tg lo cnt).
Proof.
  move => cnt; induction cnt => s tg lo.
  - simpl; destruct (isGoodIndexDec s tg lo) eqn:Good; simpl; auto.
  - simpl; destruct (isGoodIndexDec s tg lo) eqn:Good; simpl; auto.
Qed.    

Definition makeIndices (s tg : string) (lo hi : nat) : list nat :=
  makeIndicesAux s tg lo (hi - lo).

Definition makeNewIndices (sl sr tg : string) : list nat :=
  if (length tg < 2) then nil
  else makeIndices (sl ◇ sr) tg (length sl - (length tg - 1)) (length sl).

Lemma makeNewIndices_correct : forall sl sr tg,  
  List.Forall (isGoodIndex (sl ◇ sr) tg) (makeNewIndices sl sr tg).
Proof.
  move => sl sr tg.
  unfold makeNewIndices, makeIndices.
  destruct (length tg < 2); auto.
  apply makeIndicesAux_correct; auto.
Qed.

Definition shiftStringRight (tg sl sr : string) (i : nat) : nat :=
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

Lemma shiftStringRightCorrect_2 :
  forall tg sl sr i, isGoodIndex (sl ++ sr) tg (i + length sl) -> 
                     isGoodIndex sr tg i.
Proof.
  unfold isGoodIndex; move => tg sl sr i [HSub HLen]; split; simpl; auto.
  - rewrite -substring_append_left in HSub.
    simpl in *; auto.
  - rewrite <- append_length_2 in HLen; simpl in *; ssromega.
Qed.    

Lemma mapShiftZero : forall l tg input,
 [seq shiftStringRight tg "" input i | i <- l] = l.
Proof.
  induction l => tg input; simpl in *; eauto.
  rewrite IHl.
  unfold shiftStringRight; simpl; auto.
  rewrite addn0; auto.
Qed.

Lemma newIsNullLeft : forall s t,  makeNewIndices "" s t = nil.
  move => s t; unfold makeNewIndices; simpl; auto.
  destruct (String.length t < 2); simpl; auto.
Qed.

Lemma makeNewIndicesNullSmallInput (s t : string) (lo hi : nat) :
  1 + String.length s <= String.length t ->
  makeIndices s t lo hi = nil.
Proof.
  unfold makeIndices.
  remember (hi - lo) as cnt.
  move : lo hi Heqcnt s t.
  induction cnt => lo hi HCnt s t Rel; simpl; auto.
  destruct (isGoodIndexDec s t lo) as [H | H]; simpl; auto.
  - inversion H; simpl in *; ssromega.
  - eapply (IHcnt lo.+1 hi); eauto.
    ssromega.
Qed.

Lemma makeNewIndicesSmallIndex (s t : string) (lo hi : nat) :
  String.length t < 2 + String.length s ->
  1 + String.length s - String.length t <= lo ->
  lo <= hi ->
  makeIndices s t lo hi = nil.
Proof.
  unfold makeIndices.
  remember (hi - lo) as cnt.
  move: lo hi s t Heqcnt.
  induction cnt => lo hi s t Heqcnt Len1 Len2 Rel; simpl; auto.
  destruct (isGoodIndexDec s t lo) as [H | H]; simpl; auto.
  - exfalso.
    inversion H; simpl in *.
    clear H H0 IHcnt.
    ssromega.
  - eapply (IHcnt lo.+1 hi); eauto; try ssromega.
Qed.

Lemma newIsNullRight : forall s t, makeNewIndices s "" t = nil.
  move => s t.
  unfold makeNewIndices; simpl; rewrite string_app_nil_r; simpl.
  destruct (String.length t < 2) eqn:LenT; auto.
  destruct (1 + String.length s <= String.length t) eqn:Rel; auto.
  - apply makeNewIndicesNullSmallInput; auto.
  - apply makeNewIndicesSmallIndex; auto; try ssromega.
    rewrite subnBA; try ssromega.
    rewrite addnC.
    auto.
Qed.

Lemma shiftDistributive t sl sr l r :
  [seq shiftStringRight t sl sr i | i <- (l ++ r)%list ] =
  ([seq shiftStringRight t sl sr i | i <- l] ++ 
   [seq shiftStringRight t sl sr i | i <- r])%list.
Proof.
  move: t sl sr r.
  induction l => t sl sr r; simpl; auto.
  f_equal; eauto.
Qed.

Lemma shiftTwice tg input input0 input1 l1 :
   [seq shiftStringRight tg input (input0 ++ input1) i
      | i <- [seq shiftStringRight tg input0 input1 i | i <- l1]]%list =
   [seq shiftStringRight tg (input ++ input0) input1 i | i <- l1]%list.
Proof.
  move: tg input input0 input1.
  induction l1 => t x y z; simpl; auto.
  erewrite IHl1; eauto.
  f_equal.
  unfold shiftStringRight, length, chunkable_string.
  rewrite -append_length_2.
  ssromega.
Qed.


Lemma isGoodIndexSmall x y tg i :
  i + String.length tg <= String.length x ->
  isGoodIndex (x ++ y) tg i ->
  isGoodIndex x tg i.
Proof.
  move => HLen [HSub HLens]; unfold isGoodIndex in *.
  split; try ssromega.
  erewrite subStrAppendRight; eauto.
Qed.
    
Lemma concatMakeNewIndices lo hi tg x y :
  hi + String.length tg <= String.length x ->
  makeIndices (x ++ y) tg lo hi = makeIndices x tg lo hi.
Proof.
  unfold makeIndices.
  remember (hi - lo) as cnt.
  move: lo hi tg x y Heqcnt.
  induction cnt => lo hi tg x y EqCnt Len; simpl; auto.
  destruct (isGoodIndexDec (x++y) tg lo) as [H | H]; simpl in *.
  + assert (Aux: isGoodIndex x tg lo)
    by ( eapply isGoodIndexSmall; eauto; ssromega ).
    destruct (isGoodIndexDec x tg lo); try congruence; simpl; auto.
    f_equal.
    eapply IHcnt; eauto; ssromega.
  + assert (Aux : ~ isGoodIndex x tg lo).
    { 
      move => Contra.
      apply goodIndexLeft with (sr := y) in Contra.
      simpl in Contra; eauto.
    } 
    destruct (isGoodIndexDec x tg lo); try congruence; simpl; auto.
    eapply IHcnt; eauto; ssromega.
Qed.

Lemma shiftIndexesLeft xi yi zi tg :
  String.length tg <= String.length yi ->
  makeNewIndices xi (yi ◇ zi) tg = 
  makeNewIndices xi yi tg.
Proof.
  move => Len.
  destruct (String.length tg < 2) eqn:LenTG;
  unfold makeNewIndices; rewrite LenTG; simpl; auto.
  rewrite string_app_assoc.
  eapply concatMakeNewIndices; eauto.
  rewrite -append_length_2.
  ssromega.
Qed.

(* This is another place where SMT would be helpful *)
(*
Lemma auxEq xl yl tl :
  tl <= yl -> 
  (tl < 2) = false -> 
  yl - 1 - (yl - (tl - 1)) =
  (xl + yl).+1 -1 - ((xl +yl).+1 - (tl - 1)).
Proof.
  move => H1 H2.
  assert (Aux1: yl - 1 - (yl - (tl -1)) = tl - 2) by ssromega.
  rewrite Aux1.
  remember ((xl + yl).+1) as n.
  assert (tl <= n) by ssromega.
  clear Aux1 H1 Heqn xl yl.
  ssromega.
Qed.
*)

Lemma shiftIndicesAuxRight xi yi tg xl lo hi :
  xl = String.length xi ->
  [seq i + xl | i <- makeIndicesAux yi tg lo hi] =
  makeIndicesAux (xi ++ yi) tg (xl + lo) hi.
Proof.
  move: xi yi tg xl lo.
  induction hi => xi yi tg xl lo Eq; simpl; auto.
  destruct (isGoodIndexDec yi tg lo) as [Good | Good];
    simpl; eauto.
  - remember Good as Good'; clear HeqGood'.
    apply shiftStringRightCorrect with (sl := xi) in Good'; simpl in Good'.
    rewrite (addnC xl lo); subst.
    destruct (isGoodIndexDec (xi ++ yi) tg (lo + String.length xi));
      simpl; try congruence.
    f_equal; auto.
    rewrite -addnC.
    rewrite -addnS.
    eapply (IHhi xi yi tg (String.length xi) lo.+1); eauto.
  - destruct (isGoodIndexDec ((xi ++ yi)) tg (xl + lo)) as [H | H]; simpl in *.
    + assert (Hyp : xl + lo = lo + length xi) by ssromega.
      rewrite Hyp in H; clear Hyp.
      apply shiftStringRightCorrect_2 in H.
      exfalso; eauto.
    + rewrite -addnS. eapply (IHhi _ _ _ _ lo.+1); eauto.
Qed.

Lemma shiftIndexesRight xi yi zi tg :
  String.length tg <= String.length yi ->
  [seq (shiftStringRight tg xi yi i) | i <- makeNewIndices yi zi tg] =
  makeNewIndices (xi ++ yi) zi tg.
Proof.
  unfold shiftStringRight, makeNewIndices, makeIndices => H; simpl.
  destruct (String.length tg < 2) eqn:Len; auto.
  rewrite -!append_length_2.
  remember (String.length xi) as xl.
  remember (String.length yi) as yl.
  remember (String.length tg) as tl.
  assert (Aux: yl - (yl - (tl - 1)) = tl - 1)
    by ssromega.
  rewrite Aux; clear Aux; simpl.
  assert (Aux: xl + yl - (xl + yl - (tl - 1)) = tl - 1)
    by ssromega.
  rewrite Aux; clear Aux; simpl.
  remember (yl - (tl - 1)) as lo.
  assert (Aux: xl + yl - (tl - 1) = xl + lo) by ssromega.
  rewrite Aux; clear Aux; simpl.
  assert (lo > 0) by ssromega.
  remember (tl - 1) as hi.
  rewrite -string_app_assoc.
  eapply shiftIndicesAuxRight; eauto.
Qed.

Lemma forall_append {A} P (l1 l2 : list A):
  List.Forall P l1 -> List.Forall P l2 -> 
  List.Forall P (l1 ++ l2) .
Proof.
  move: l2.
  induction l1=> l2 H1 H2; simpl; auto.
  constructor; inversion H1; eauto.
Qed.

Definition sm_nil tg := Sm tg "" nil.
Definition sm_mappend tg (sm1 sm2 : SM tg) := 
  let '(Sm x xis) := sm1 in
  let '(Sm y yis) := sm2 in 
  let xis' := xis in 
  let xyis := makeNewIndices x y tg in
  let yis' := map (shiftStringRight tg x y) yis in
  Sm tg (x ◇ y) (List.app xis' (List.app xyis yis')).

Theorem sm_id_left tg (sm : SM tg) : 
  sm_mappend tg (sm_nil tg) sm = sm.
Proof. 
  simpl.
  destruct sm; simpl.
  rewrite (mapShiftZero l tg input). 
  rewrite newIsNullLeft; simpl; auto.
Qed.

Theorem sm_id_right tg (sm : SM tg) :
  sm_mappend tg sm (sm_nil tg) = sm.
  simpl. destruct sm; simpl.
  rewrite string_app_nil_r.
  rewrite newIsNullRight.
  simpl; auto; rewrite List.app_nil_r; simpl; auto.
Qed.

Lemma shiftStringRight_append_front xi yi tg lo hi :
  lo <= hi ->
  [seq shiftStringRight tg xi yi i
  | i <- makeIndices yi tg lo hi ] = 
  makeIndices (xi ++ yi) tg (lo + String.length xi) (hi + String.length xi).
Proof.
  remember (hi - lo) as cnt.
  move: lo hi Heqcnt xi yi tg.
  induction cnt => lo hi CNT xi yi tg Rel; simpl; auto.
  - assert (hi = lo) by ssromega; subst.
    unfold makeIndices, makeIndicesAux.
    rewrite -CNT; simpl; auto.
    assert (lo + String.length xi - (lo + String.length xi) = 0) by ssromega.
    rewrite H.
    auto.
  - unfold makeIndices.
    assert (Aux: hi + String.length xi - (lo + String.length xi) = hi - lo)
           by ssromega.
    rewrite Aux.
    rewrite -CNT.
    unfold shiftStringRight, length, chunkable_string.
    remember (String.length xi) as xl.
    rewrite addnC.
    eapply shiftIndicesAuxRight; eauto.
Qed.    

Lemma makeIndicesSplit mid s tg lo hi :
  lo <= mid -> mid <= hi ->
  makeIndices s tg lo hi = 
  (makeIndices s tg lo mid ++ makeIndices s tg mid hi)%list.
Proof.
  unfold makeIndices.
  remember (mid - lo) as cnt.
  move: s tg mid lo hi Heqcnt.
  induction cnt => s tg mid lo hi CNT Lt1 Lt2; simpl; auto.
  - assert (mid = lo) by ssromega; subst; auto.
  - destruct (hi - lo) eqn:HILO; try ssromega; simpl.
    destruct (isGoodIndexDec s tg lo); simpl; auto; [f_equal |];
    assert (Aux : n = hi - lo.+1) by ssromega; rewrite Aux;
    eapply (IHcnt _ _ _ lo.+1 hi); eauto; ssromega.
Qed.

Theorem sm_mappend_assoc tg (sm1 sm2 sm3 : SM tg) :
  validSM tg sm1 -> validSM tg sm2 -> validSM tg sm3 -> 
  sm_mappend tg sm1 (sm_mappend tg sm2 sm3) =
  sm_mappend tg (sm_mappend tg sm1 sm2) sm3.
Proof.
  simpl.
  move => v1 v2 v3; 
  destruct sm1 as [xi xs]; 
  destruct sm2 as [yi ys];
  destruct sm3 as [zi zs]; simpl; auto.
  rewrite string_app_assoc; simpl; auto.
  f_equal.
  rewrite -List.app_assoc; auto.
  f_equal.
  rewrite -!List.app_assoc; auto.
  erewrite shiftDistributive; eauto.
  erewrite shiftDistributive; eauto.
  erewrite shiftTwice; eauto.
  rewrite !List.app_assoc; auto.
  f_equal.
  (* This is the actual assocNewIndices I think. 
     Renaming for compatibility *)
  destruct (String.length tg <= String.length yi) eqn:LenTgYi.
  + rewrite shiftIndexesLeft; eauto.
    rewrite -!List.app_assoc; auto.
    f_equal.
    unfold shiftStringRight; simpl; auto.
    f_equal.
    apply shiftIndexesRight; eauto.
  + inversion v2 as [input l Hyp]; subst.
    destruct ys; simpl in *; auto.
    * rewrite !List.app_nil_r.
      clear Hyp.
      { 
        unfold makeNewIndices; simpl.
        destruct (String.length tg < 2) eqn:LenTG; simpl; auto.
        rewrite string_app_assoc.
        rewrite -!append_length_2.
        remember (String.length xi) as xl.
        remember (String.length yi) as yl.
        remember (String.length zi) as zl.
        remember (String.length tg) as tl.
        assert (Sub0: yl - (tl - 1) = 0) by ssromega.
        rewrite Sub0.
        destruct (xl + yl < tl) eqn:Rel.
        - (* Target greater than the first two strings *)
          assert (Aux : makeIndices (xi ++ yi) tg (xl - (tl - 1)) xl = nil).
          { 
            subst.
            apply makeNewIndicesNullSmallInput.
            rewrite -append_length_2.
            ssromega.
          } 
          rewrite Aux; simpl.
          destruct (tl <= yl + zl) eqn:Rel2.
          + rewrite (shiftIndicesAuxRight xi); auto.
            rewrite addn0.
            rewrite subn0.
            unfold makeIndices.
            assert (Aux' : xl + yl - (tl - 1) = 0) by ssromega; rewrite Aux'; clear Aux'.
            assert (Aux' : xl - (tl - 1) = 0) by ssromega; rewrite Aux'; clear Aux'.
            rewrite !subn0.
            rewrite string_app_assoc.
            simpl; rewrite -Heqxl.
            destruct (yl == 0) eqn:YL0; auto.
            * assert (yl = 0) by ssromega.
              rewrite !H. simpl. rewrite addn0. rewrite List.app_nil_r; auto.
            * assert (H1 : 0 <= xl) by auto.
              assert (H2: xl <= xl + yl) by ssromega.
              pose proof (makeIndicesSplit xl ((xi ++ yi) ++ zi) tg 0 (xl + yl) H1 H2) as H.
              unfold makeIndices in H.
              rewrite !subn0 in H.
              rewrite H.
              f_equal.
              rewrite addnC.
              assert (H0 : yl + xl - xl = yl) by ssromega.
              rewrite H0; auto.
          + assert (Aux': makeIndices (yi ++ zi) tg 0 yl = nil).
            {
              subst.
              apply makeNewIndicesNullSmallInput.
              rewrite -append_length_2.
              ssromega.
            } 
            rewrite Aux'; clear Aux'.
            simpl.
            rewrite List.app_nil_r.
            (* Break into two parts each *)
            rewrite (makeIndicesSplit (xl + yl - (tl - 1))); try ssromega.
            symmetry.
            rewrite (makeIndicesSplit xl); try ssromega.
            assert (Hyp: makeIndices ((xi ++ yi) ++ zi) tg xl (xl + yl) = nil).
            {
              destruct (tl <= xl + yl + zl) eqn:TooLarge; auto; subst.
              - eapply makeNewIndicesSmallIndex; eauto;
                try rewrite -!append_length_2;
                try ssromega.
                (* Another place where Z3 would just work *)
                assert (Hyp: 1 + (String.length xi + String.length yi + String.length zi) 
                           = String.length xi + (1 + String.length yi + String.length zi))
                       by ssromega.
                rewrite Hyp; clear Hyp.
                ssromega.
              - eapply makeNewIndicesNullSmallInput; eauto.
                rewrite -!append_length_2; ssromega.
            } 
            rewrite Hyp List.app_nil_r.
            assert (Aux' : xl + yl - (tl - 1) = 0) by ssromega; rewrite Aux'; clear Aux'.
            simpl; auto.
        - admit.
      } 
    * inversion Hyp; subst.
      inversion H1; simpl in *; ssromega.
Admitted.



(* Intrinsic is needed for the monoid instance with a monoid instance... *)
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
(* 
Next Obligation.
  eapply forall_append; eauto.
  - induction xis; auto. 
    constructor; inversion pf1; subst; eauto. 
    apply goodIndexLeft; eauto.
  - eapply forall_append; eauto.
    + apply makeNewIndices_correct. 
    + induction yis; simpl; auto.
      constructor; inversion pf2; subst; eauto.
      unfold shiftStringRight; simpl; auto.
      eapply shiftStringRightCorrect; eauto.
Defined. *)
- simpl.
  move => x y z; destruct x; destruct y; destruct z; simpl; auto.
  rewrite string_app_assoc; simpl; auto.
  f_equal.
  rewrite -List.app_assoc; auto.
  f_equal.
  rewrite -!List.app_assoc; auto.
  erewrite shiftDistributive; eauto.
  erewrite shiftDistributive; eauto.
  erewrite shiftTwice; eauto.
  rewrite !List.app_assoc; auto.
  f_equal.
  (* This is the actual assocNewIndices I think. 
     Renaming for compatibility *)
  move: target input input0 input1 l l0 l1 => 
        tg     xi yi zi x y z.
  destruct (String.length tg <= String.length yi) eqn:LenTgYi.
  + rewrite shiftIndexesLeft; eauto.
    rewrite -!List.app_assoc; auto.
    f_equal.
    unfold shiftStringRight; simpl; auto.
    f_equal.
    apply shiftIndexesRight; eauto.
  + 


Admitted.
  
  

emptyIndices :: forall (target :: Symbol). (KnownSymbol target) => SM target -> List Int  -> Proof
{-@ emptyIndices :: mi:SM target
                 -> is:{List (GoodIndex (inputSM mi) target) | is == indicesSM mi && stringLen (inputSM mi) < stringLen target}
                 -> { is == N } @-}
emptyIndices (SM _ _) N 
  = trivial 
emptyIndices (SM _ _) (C _ _)
  = trivial 
