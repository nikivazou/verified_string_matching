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
{-@ LIQUID "--trust-internals"     @-}


{-@ infix   <+> @-}

import Language.Haskell.Liquid.ProofCombinators 



import Prelude hiding ( mempty, mappend, mconcat, map, Monoid
                      , take, drop  
                      , error, undefined
                      )

import Control.Parallel.Strategies 
import GHC.TypeLits
import RString.RString

#include "RList.hs"
#include "MList.hs"
#include "PMonoid.hs"
#include "RString/Chunk.hs"
#include "DistributeInput.hs"


{-@ distributionEq :: _ -> is:RString -> n:Integer -> {toMonoid is == mconcat (map toMonoid (chunkString n is))} @-}
distributionEq :: forall (a :: Symbol). (KnownSymbol a) => Monoid a -> RString -> Integer -> Proof
distributionEq _ is n = distributeInput (toMonoid :: RString -> Monoid a) (distributestoMonoid (mempty :: Monoid a)) is n 

{-@ reflect toMonoid @-}
toMonoid :: RString -> Monoid a 
toMonoid _ = M


{-@ distributestoMonoid :: _ -> x1:RString -> x2:RString -> {toMonoid (x1 <+> x2) ==  (toMonoid x1) <> (toMonoid x2)} @-}
distributestoMonoid :: forall (a :: Symbol). (KnownSymbol a) => Monoid a -> RString -> RString -> Proof 
distributestoMonoid _ x1 x2
  =   toMonoid (x1 <+> x2)
  ==. (M :: Monoid a)
  ==. (M :: Monoid a) <> (M :: Monoid a) 
  ==. (toMonoid x1) <> (toMonoid x2)
  *** QED 
