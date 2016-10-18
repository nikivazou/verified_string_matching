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

{-@ LIQUID "--higherorder"         @-}
{-@ LIQUID "--totality"            @-}
{-@ LIQUID "--exactdc"             @-}
{-@ LIQUID "--trust-internals"     @-}

{-@ infix <+> @-}
{-@ infix <>  @-}


import Language.Haskell.Liquid.ProofCombinators 



import Prelude hiding ( mempty, mappend, mconcat, map, Monoid
                      , take, drop  
                      , error, undefined
                      )

import Control.Parallel.Strategies 
import GHC.TypeLits
import RString.RString
import Data.Proxy

#define CheckDistributeInput
#define CheckMonoidEmptyLeft
#define CheckMonoidEmptyRight

#define MainCall

#include "RList.hs"
#include "PMonoid.hs"
#include "RString/Chunk.hs"
#include "DistributeInput.hs"
#include "DistributeToSM.hs"
#include "StringMatching.hs"

#include "MonoidEmptyLeft.hs"
#include "MonoidEmptyRight.hs"

#include "ListMonoidLemmata.hs"
#include "CastLemmata.hs"
#include "EmptyLemmata.hs"
#include "ListLemmata.hs"
#include "ShiftingLemmata.hs"


type Monoid a = SM a 
#endif 


{-@ distributionEq :: _ -> is:RString -> n:Int -> {toSM is == mconcat (map toSM (chunkString n is))} @-}
distributionEq :: forall (a :: Symbol). (KnownSymbol a) => SM a -> RString -> Int -> Proof

#ifdef CheckDistributeInput
distributionEq _ is n = distributeInput (toSM :: RString -> SM a) (distributestoSM (mempty :: SM a)) is n 


#else 
distributionEq _ _ _ = trivial 
#endif 
