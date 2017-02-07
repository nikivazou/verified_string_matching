{-# LANGUAGE CPP                 #-}

#ifdef MainCall
#else  
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE CPP                 #-}

{-@ LIQUID "--higherorder"         @-}
{-@ LIQUID "--totality"            @-}
{-@ LIQUID "--exactdc"             @-}
{-@ LIQUID "--no-measure-fields"   @-}
{-@ LIQUID "--trust-internals"     @-}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}

{-@ infix <+> @-}
{-@ infix <>  @-}

import Data.RString.RString
import Language.Haskell.Liquid.ProofCombinators 

import Data.Proxy 
import GHC.TypeLits

import Prelude hiding ( mempty, mappend, id, mconcat, map
                      , take, drop  
                      , error, undefined 
                      )
#define MainCall

#include "../Data/List/RList.hs"  
#include "../Data/StringMatching/StringMatching.hs"
#include "../Proofs/ListMonoidLemmata.hs"



#define CheckMonoidAssoc
#endif

#ifdef IncludedListLemmata
#else  
#include "../Proofs/ListLemmata.hs"   
#endif

#ifdef IncludedshiftNewIndices
#else  
#include "../Proofs/shiftNewIndices.hs"   
#endif

#ifdef IncludedemptyIndices
#else  
#include "../Proofs/emptyIndices.hs"   
#endif

#ifdef IncludedcastShift
#else  
#include "../Proofs/castShift.hs"   
#endif

#ifdef IncludedshiftNewIndicesRight
#else  
#include "../Proofs/shiftNewIndicesRight.hs"   
#endif


#ifdef IncludedshiftNewIndicesLeft
#else  
#include "../Proofs/shiftNewIndicesLeft.hs"   
#endif


#ifdef IncludedmapLenFusion
#else  
#include "../Proofs/mapLenFusion.hs"   
#endif

#ifdef IncludedcastConcat
#else  
#include "../Proofs/castConcat.hs"   
#endif

#define IncludedMonoidAssoc

#ifdef CheckMonoidAssoc 

{-@ automatic-instances mappend_assoc @-}

{-@ mappend_assoc :: x:SM target -> y:SM target -> z:SM target -> { x <> (y <> z) = (x <> y) <> z} @-}
mappend_assoc
     :: forall (target :: Symbol). (KnownSymbol target) 
     => SM target ->  SM target ->  SM target -> Proof

mappend_assoc x@(SM xi xis) y@(SM yi yis) z@(SM zi zis)
  =   stringAssoc xi yi zi 
  &&& mapAppend (shiftStringRight tg xi (yi <+> zi)) (yzileft `append` yzinew) yziright 
  &&& mapAppend (shiftStringRight tg xi (yi <+> zi)) yzileft yzinew 
  &&& appendGroup is1left is2left is3left is4left is5left
  &&& assocNewIndices y tg xi yi zi yis
  &&& castConcat tg xi yi zi xis 
  &&& mapLenFusion tg xi yi zi zis
  &&& appendUnGroup is1right is2right is3right is4right is5right
  &&& mapAppend (castGoodIndexRight tg (xi <+> yi) zi) xyileft xyinew
  &&& mapAppend (castGoodIndexRight tg (xi <+> yi) zi) (xyileft `append` xyinew) xyiright
  where
        tg         = fromString (symbolVal (Proxy :: Proxy target))
        yzileft    = map (castGoodIndexRight tg yi zi) yis
        yzinew     = makeNewIndices yi zi tg
        yziright   = map (shiftStringRight tg yi zi) zis
        yzi        = yzileft `append` yzinew `append` yziright
        xyzi       = is1left `append` is2left `append` xyiright

        is1left    = map (castGoodIndexRight tg xi (yi <+> zi)) xis

        is2left    = makeNewIndices xi (yi <+> zi) tg
        is3left    = map (shiftStringRight tg xi (yi <+> zi)) yzileft
        is4left    = map (shiftStringRight tg xi (yi <+> zi)) yzinew

        is5left    = map (shiftStringRight tg xi (yi <+> zi)) yziright

        is1right   = map (castGoodIndexRight tg (xi <+> yi) zi) xyileft
        is2right   = map (castGoodIndexRight tg (xi <+> yi) zi) xyinew
        is3right   = map (castGoodIndexRight tg (xi <+> yi) zi) xyiright
        is4right   = makeNewIndices (xi <+> yi) zi tg
        is5right   = map (shiftStringRight tg (xi <+> yi) zi) zis

        xyileft    = map (castGoodIndexRight tg xi yi) xis
        xyinew     = makeNewIndices xi yi tg
        xyiright   = map (shiftStringRight tg xi yi) yis

        input      = xi <+> (yi <+> zi)





{-@ inline makeIs2left @-}
{-@ inline makeIs3left @-}
{-@ inline makeIs4left @-}

makeIs2left tg xi yi zi = makeNewIndices xi (yi <+> zi) tg
{-@ makeIs3left :: tg:RString -> xi:RString -> yi:RString -> zi:RString -> List (GoodIndex yi tg) -> List Int @-} 
makeIs3left :: RString -> RString -> RString -> RString -> List Int -> List Int 
makeIs3left tg xi yi zi yis   
  = map (shiftStringRight tg xi (yi <+> zi)) (map (castGoodIndexRight tg yi zi) yis)
makeIs4left tg xi yi zi     
  = map (shiftStringRight tg xi (yi <+> zi)) (makeNewIndices yi zi tg)

{-@ inline makeIs3right @-}
{-@ inline makeIs4right @-}
{-@ inline makeIs2right @-}
makeIs2right tg xi yi zi = map (castGoodIndexRight tg (xi <+> yi) zi) (makeNewIndices xi yi tg) 
{-@ makeIs3right :: tg:RString -> xi:RString -> yi:RString -> zi:RString -> List (GoodIndex yi tg) -> List Int @-} 
makeIs3right tg xi yi zi yis   
  = map (castGoodIndexRight tg (xi <+> yi) zi) (map (shiftStringRight tg xi yi) yis)
makeIs4right tg xi yi zi     
  = makeNewIndices (xi <+> yi) zi tg


{-@ automatic-instances assocNewIndices @-}

assocNewIndices :: forall (target :: Symbol). (KnownSymbol target) => 
  SM target -> RString -> RString -> RString -> RString -> List Int -> Proof
{-@ assocNewIndices :: y:SM target -> tg:{RString | tg == target} -> xi:RString 
   -> yi:{RString | yi == inputSM y} 
   -> zi:RString 
   -> yis:{List (GoodIndex (inputSM y) tg) | yis == indicesSM y }  
   -> { append (append (makeIs2left  tg xi yi zi) (makeIs3left  tg xi yi zi yis)) (makeIs4left  tg xi yi zi) == 
        append (append (makeIs2right tg xi yi zi) (makeIs3right tg xi yi zi yis)) (makeIs4right tg xi yi zi)}  @-}
assocNewIndices y tg xi yi zi yis 
  | stringLen tg <= stringLen yi 
  =   shiftNewIndicesLeft  xi yi zi tg 
  &&& castShift tg xi yi zi yis  
  &&& shiftNewIndicesRight xi yi zi tg 
  *** QED 
  | stringLen yi < stringLen tg
  =   is2left  `append` is3left  `append` is4left
  ==. is2left  `append` N  `append` is4left
      ? emptyIndices y yis 
  ==. is2left `append` is4left
      ? listLeftId is2left
  ==. is2right `append` is4right 
      ? shiftNewIndices xi yi zi tg 
  ==. (is2right `append` N) `append` is4right 
      ? listLeftId is2right
  ==. (is2right `append` is3right) `append` is4right 
      ? emptyIndices y yis 
  *** QED 

    where
        is2left    = makeNewIndices xi (yi <+> zi) tg
        is3left    = map (shiftStringRight tg xi (yi <+> zi)) yzileft
        is4left    = map (shiftStringRight tg xi (yi <+> zi)) yzinew

        is2right   = map (castGoodIndexRight tg (xi <+> yi) zi) xyinew
        is3right   = map (castGoodIndexRight tg (xi <+> yi) zi) xyiright
        is4right   = makeNewIndices (xi <+> yi) zi tg


        yzileft    = map (castGoodIndexRight tg yi zi) yis
        yzinew     = makeNewIndices yi zi tg

        xyinew     = makeNewIndices xi yi tg
        xyiright   = map (shiftStringRight tg xi yi) yis

#else
{-@ mappend_assoc :: x:SM target -> y:SM target -> z:SM target -> { x <> (y <> z) = (x <> y) <> z} @-}
mappend_assoc
     :: forall (target :: Symbol). (KnownSymbol target) 
     => SM target ->  SM target ->  SM target -> Proof

mappend_assoc _ _ _ = trivial  
#endif

