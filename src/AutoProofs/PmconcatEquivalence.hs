{-# LANGUAGE CPP                  #-}
#ifdef MainCall

type Monoid a = SM a 

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
{-@ LIQUID "--trust-internals"     @-}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}

{-@ infix <+> @-}
{-@ infix <> @-}

import Language.Haskell.Liquid.ProofCombinators 



import Prelude hiding ( mempty, mappend, mconcat, map, Monoid
                      , take, drop  
                      , error, undefined
                      )

import Control.Parallel.Strategies 
import GHC.TypeLits

import Data.RString.RString 

#define CheckParEquivalence
#define ParallelEvaluation

#include "../Data/List/RList.hs"
#include "../Data/RString/Chunk.hs"
#include "../Data/List/MList.hs"
#include "../Data/Monoid/PMonoid.hs"
#include "../AutoProofs/DistributeInput.hs"

#endif

{-@ automatic-instances parallelismEquivalence   @-}
{-@ parallelismEquivalence :: 
      f:(RString -> Monoid target) 
   -> (x1:RString -> x2:RString -> {f (x1 <+> x2) ==  (f x1) <> (f x2)})
   -> is:RString  -> n:Int -> m:Int
   -> {f is == pmconcat m (map f (chunkString n is)) } @-}

parallelismEquivalence :: forall (target :: Symbol). (KnownSymbol target) 
  => (RString -> Monoid target)
  -> (RString -> RString -> Proof) 
  -> RString -> Int -> Int -> Proof
parallelismEquivalence f thm is n m  
  =   pmconcatEquivalence m (map f (chunkString n is) :: List (Monoid target))
  &&& distributeInput f thm is n 
  *** QED  



pmconcatEquivalence :: forall (a :: Symbol). (KnownSymbol a) => Int -> List (Monoid a) -> Proof
{-@ pmconcatEquivalence :: i:Int -> is:List (Monoid a) -> {pmconcat i is == mconcat is} / [llen is] @-}

#ifdef CheckParEquivalence

{-@ automatic-instances pmconcatEquivalence   @-}

pmconcatEquivalence i is 
  | i <= 1
  = trivial
pmconcatEquivalence i N 
  =   trivial
pmconcatEquivalence i (C x N) 
  = mempty_left x
pmconcatEquivalence i xs 
  | llen xs <= i 
  = trivial
pmconcatEquivalence i xs
  =   pmconcat i xs
  ==. mconcat xs 
  ?   mconcatChunk i xs &&& pmconcatEquivalence i (map mconcat (chunk i xs))
  *** QED 

-- | Monoid implications 

{-@ automatic-instances mconcatSplit   @-}

mconcatSplit :: forall (a :: Symbol). (KnownSymbol a) => Int -> List (Monoid a) -> Proof 
{-@ mconcatSplit :: i:Nat -> xs:{List (Monoid a) | i <= llen xs} 
     -> { mconcat xs ==  mconcat (take i xs) <> mconcat (drop i xs)}
     / [i]
  @-} 
mconcatSplit i N 
  = mempty_left (mempty :: Monoid a)
mconcatSplit i (C x xs)
  | i == 0
  = mempty_right (mconcat (C x xs))
  *** QED 
  | otherwise    
  =   mappend_assoc x (mconcat (take (i-1) xs)) (mconcat (drop (i-1) xs))
  &&& mconcatSplit (i-1) xs

-- Generalization to chunking  

mconcatChunk :: forall (a :: Symbol). (KnownSymbol a) => Int -> List (Monoid a) -> Proof 
{-@ mconcatChunk :: i:Pos -> xs:List (Monoid a) 
  -> { mconcat xs == mconcat (map mconcat (chunk i xs))}
  /  [llen xs] @-}
mconcatChunk i xs  
  | llen xs <= i 
  =   mconcat (map mconcat (chunk i xs))
  ==. mconcat (map mconcat (C xs N))
  ==. mconcat (mconcat xs `C` map mconcat N)
  ==. mconcat xs <> mconcat N
  ==. mconcat xs 
       ? mempty_left (mconcat xs)
  *** QED  
   | otherwise
   =   mconcat (map mconcat (chunk i xs))
   ==. mconcat (map mconcat (take i xs `C` chunk i (drop i xs)))
   ==. mconcat (mconcat (take i xs) `C` map mconcat (chunk i (drop i xs)))
   ==. mconcat (take i xs) <> (mconcat (drop i xs))
        ? mconcatChunk i (drop i xs)
   ==. mconcat xs 
        ? mconcatSplit i xs 
   *** QED 


#else
pmconcatEquivalence _ _ = trivial     
#endif

