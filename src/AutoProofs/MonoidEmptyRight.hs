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

#define CheckMonoidEmptyRight
#endif

#ifdef IncludedmakeNewIndicesNullRight
#else
#include "../Proofs/makeNewIndicesNullRight.hs"
#endif

#ifdef IncludedmapShiftZero
#else
#include "../Proofs/mapShiftZero.hs"
#endif

#define IncludedMonoidEmptyRight

#ifdef CheckMonoidEmptyRight

{-@ automatic-instances smRightId @-}

smRightId :: forall (target :: Symbol). (KnownSymbol target) => SM target -> Proof
{-@ smRightId :: xs:SM target -> {mempty <> xs == xs } @-}
smRightId (SM i is)
  =   let tg = (fromString (symbolVal (Proxy :: Proxy target))) in 
      stringRightId i
  &&& makeNewIndicesNullRight i tg
  &&& mapShiftZero tg i is 

mempty_right :: forall (target :: Symbol). (KnownSymbol target) => SM target -> Proof
{-@ mempty_right :: xs:SM target -> {mempty <> xs == xs } @-}
mempty_right = smRightId


#else
mempty_right :: forall (target :: Symbol). (KnownSymbol target) => SM target -> Proof
{-@ mempty_right :: xs:SM target -> {mempty <> xs == xs } @-}
mempty_right _ = trivial   
#endif

