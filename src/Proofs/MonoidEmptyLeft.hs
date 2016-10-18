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

import RString.RString
import Language.Haskell.Liquid.ProofCombinators 

import Data.Proxy 
import GHC.TypeLits

import Prelude hiding ( mempty, mappend, id, mconcat, map
                      , take, drop  
                      , error, undefined
                      )
#include "RList.hs"
#include "StringMatching.hs"

#include "ListMonoidLemmata.hs"
#include "EmptyLemmata.hs"
#include "CastLemmata.hs"
#include "ShiftingLemmata.hs"

#define CheckMonoidEmptyLeft
#endif

mempty_left :: forall (target :: Symbol). (KnownSymbol target) => SM target -> Proof
{-@ mempty_left :: xs:SM target -> {xs <> mempty == xs } @-}
#ifdef CheckMonoidEmptyLeft
mempty_left (SM i is) 
  = let tg = fromString (symbolVal (Proxy :: Proxy target)) in 
      (SM i is) <> (mempty :: SM target)
  ==. (SM i is) <> (SM stringEmp N) 
  ==. SM ((<+>) i stringEmp)
         ((map (castGoodIndexRight tg i stringEmp) is
            `append`
           makeNewIndices i stringEmp tg 
         ) `append`
         (map (shiftStringRight tg i stringEmp) N))
      ? concatStringNeutralLeft i 
  ==. SM i
         ((map (castGoodIndexRight tg i stringEmp) is
            `append`
           makeNewIndices i stringEmp tg
         ) `append`
         (map (shiftStringRight tg i stringEmp) N))
      ? mapCastId tg i stringEmp is
  ==. SM i ((is `append` N) `append` (map (shiftStringRight tg i stringEmp) N))
      ? makeNewIndicesNullLeft i tg 
  ==. SM i (is `append` map (shiftStringRight tg i stringEmp) N)
      ? appendNil is  
  ==. SM i (is `append` N)
      ? appendNil is  
  ==. SM i is 
  *** QED 



#else
mempty_left _ = trivial  
#endif
