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

#define CheckMonoidEmptyLeft
#endif

#ifdef IncludedmakeNewIndicesNullLeft
#else  
#include "../AutoProofs/makeNewIndicesNullLeft.hs"   
#endif

#ifdef IncludedmapCastId
#else  
#include "../AutoProofs/mapCastId.hs"   
#endif

#define IncludedMonoidEmptyLeft

#ifdef CheckMonoidEmptyLeft

{-@ automatic-instances smLeftId @-}

smLeftId :: forall (target :: Symbol). (KnownSymbol target) => SM target -> Proof
{-@ smLeftId :: xs:SM target -> {xs <> mempty == xs } @-}
smLeftId (SM i is) 
  = let tg = fromString (symbolVal (Proxy :: Proxy target)) in 
      stringLeftId i 
  &&& mapCastId tg i stringEmp is
  &&& makeNewIndicesNullLeft i tg 
  &&& listLeftId is  


mempty_left :: forall (target :: Symbol). (KnownSymbol target) => SM target -> Proof
{-@ mempty_left :: xs:SM target -> {xs <> mempty == xs } @-}
mempty_left = smLeftId
#else
mempty_left :: forall (target :: Symbol). (KnownSymbol target) => SM target -> Proof
{-@ mempty_left :: xs:SM target -> {xs <> mempty == xs } @-}
mempty_left _ = trivial  
#endif
