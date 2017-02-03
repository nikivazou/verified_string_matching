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
#define CheckMonoidEmptyLeft
#define CheckMonoidEmptyRight

#include "../Data/List/RList.hs"
#include "../Data/StringMatching/StringMatching.hs"

#include "../Proofs/MonoidEmptyLeft.hs"
#include "../Proofs/MonoidEmptyRight.hs"

#include "../Proofs/ListMonoidLemmata.hs"
#include "../Proofs/CastLemmata.hs"
#include "../Proofs/EmptyLemmata.hs"
#include "../Proofs/ListLemmata.hs"
#include "../Proofs/ShiftingLemmata.hs"

#define CheckDistributeInput
#endif



#ifdef CheckDistributeInput
distributestoSM :: forall (target :: Symbol). (KnownSymbol target) => SM target -> RString -> RString -> Proof 
{-@ distributestoSM :: SM target -> x1:RString -> x2:RString 
  -> {toSM (x1 <+> x2) ==  (toSM x1) <> (toSM x2)} @-} 
distributestoSM x x1 x2
  | stringLen x1 == 0 
  =   (toSM x1) <> (toSM x2)
  ==. (mempty :: SM target) <> (toSM x2 :: SM target)
       ? toSMEmpty x x1
  ==. toSM x2 
      ? mempty_right (toSM x2 :: SM target)
  ==. toSM (x1 <+> x2)
      ? concatEmpLeft x1 x2 
  *** QED 

distributestoSM x x1 x2
  | stringLen x2 == 0 
  =   (toSM x1) <> (toSM x2)
  ==. (toSM x1) <> (mempty :: SM target)
      ? toSMEmpty x x2  
  ==. (toSM x1 :: SM target)
      ? mempty_left (toSM x1 :: SM target)
  ==. toSM (x1 <+> x2)
      ? concatEmpRight x1 x2 
  *** QED 

distributestoSM _ x y 
  =   (toSM x :: SM target) <> (toSM y :: SM target)  
  ==. (SM x is1) <> (SM y is2)
  ==. SM i (xis `append` xyis `append` yis)
  ==. SM i (makeIndices i tg 0 hi1 `append` yis) 
       ?(mapCastId tg x y is1 &&& mergeNewIndices tg x y)
  ==. SM i (makeIndices i tg 0 hi1 `append` makeIndices i tg (hi1+1) hi) 
      ? shiftIndicesRight 0 hi2 x y tg 
  ==. SM i is
      ? mergeIndices i tg 0 hi1 hi
  ==. toSM (x <+> y)
  *** QED 
  where
    xis  = map (castGoodIndexRight tg x y) is1
    xyis = makeNewIndices x y tg
    yis  = map (shiftStringRight   tg x y) is2

    tg  = fromString (symbolVal (Proxy :: Proxy target))
    is1 = makeSMIndices x tg 
    is2 = makeSMIndices y tg 
    is  = makeSMIndices i tg 

    i = x <+> y

    hi1 = stringLen x - 1
    hi2 = stringLen y - 1
    hi  = stringLen i - 1  


{-@ type RStringNE = {v:RString | 0 < stringLen v } @-}

mergeNewIndices :: RString -> RString -> RString -> Proof
{-@ mergeNewIndices :: tg:RString -> x1:RStringNE -> x2:RStringNE 
  -> {append (makeSMIndices x1 tg) (makeNewIndices x1 x2 tg) == makeIndices (x1 <+> x2) tg 0 (stringLen x1 - 1)} @-}
mergeNewIndices tg x1 x2  
  | stringLen tg < 2 
  =   makeSMIndices x1 tg        `append` makeNewIndices x1 x2 tg
  ==. makeIndices x1 tg 0 hi     `append` makeNewIndices x1 x2 tg
  ==. makeIndices x1 tg 0 hi     `append` N
  ==. makeIndices x1 tg 0 hi 
      ? appendNil (makeIndices x1 tg 0 hi)
  ==. makeIndices x  tg 0 hi
      ? concatmakeNewIndices 0 hi tg x1 x2
  *** QED 
  | stringLen x1  < stringLen tg
  =   makeSMIndices x1 tg        `append` makeNewIndices x1 x2 tg
  ==. makeIndices x1 tg 0 hi     `append` makeNewIndices x1 x2 tg
  ==. N                          `append` makeIndices x tg 0  hi
      ? makeNewIndicesNullSmallInput x1 tg 0 hi
  ==. makeIndices x  tg 0 hi
  *** QED 
  | otherwise {- stringLen tg <= stringLen x1 -}
  =   makeSMIndices x1 tg     `append` makeNewIndices x1 x2 tg
  ==. makeIndices x1 tg 0 hi  `append` makeNewIndices x1 x2 tg
  ==. makeIndices x1 tg 0 hi  `append` makeIndices x tg lo hi
  ==. makeIndices x  tg 0 mid `append` makeIndices x tg (mid+1) hi 
      ? catIndices x1 x2 tg 0 hi
  ==. makeIndices x  tg 0 hi
      ? mergeIndices x tg 0 mid hi
  *** QED 
  where
    x   = x1 <+> x2

    lo  = maxInt (mid+1) 0
    mid = stringLen x1 - stringLen tg
    hi  = stringLen x1 - 1

#else
distributestoSM :: forall (target :: Symbol). (KnownSymbol target) => SM target -> RString -> RString -> Proof 
{-@ distributestoSM :: SM target -> x1:RString -> x2:RString 
  -> {toSM (x1 <+> x2) ==  (toSM x1) <> (toSM x2)} @-} 
distributestoSM _ _ _ = trivial 
#endif

