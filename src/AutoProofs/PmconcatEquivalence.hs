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
{-@ LIQUID "--no-measure-fields"   @-}
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

#endif

#ifdef IncludeddistributeInput
#else  
#include "../Proofs/DistributeInput.hs"
#endif
IncludeddistributeInput


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

#ifdef CheckParEquivalence

{-@ automatic-instances pmconcatEquivalence   @-}

pmconcatEquivalence :: forall (a :: Symbol). (KnownSymbol a) => Int -> List (Monoid a) -> Proof
{-@ pmconcatEquivalence :: i:Int -> is:List (Monoid a) -> {pmconcat i is == mconcat is} / [llen is] @-}
pmconcatEquivalence i is 
  | i <= 1 || llen is <= i 
  = trivial  
pmconcatEquivalence i issssss
  =   pmconcatEquivalence i (map mconcat (chunk i issssss))
  &&& mconcatChunk i issssss

-- NV The above needs intermediate calculations, 
-- bevause pmconcat i is == pmconcat (map mconcat (chunk i is))
-- is all I need but chunk can get further evaluated

-- | Monoid implications 

{-@ automatic-instances mconcatSplit   @-}

{- 
NV: Note the unfolding here required becuase of the complicated SM type
It is not required when I run only this file and not the SM 
-}

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
  | otherwise    
  =   mappend_assoc x (mconcat (take (i-1) xs)) (mconcat (drop (i-1) xs))
  &&& mconcatSplit (i-1) xs

-- Generalization to chunking  

{-@ automatic-instances mconcatChunk @-}
mconcatChunk :: forall (a :: Symbol). (KnownSymbol a) => Int -> List (Monoid a) -> Proof 
{-@ mconcatChunk :: i:Pos -> xs:List (Monoid a) 
  -> { mconcat xs == mconcat (map mconcat (chunk i xs))}
  /  [llen xs] @-}
mconcatChunk i xs  
  | llen xs <= i 
  = mempty_left (mconcat xs)
  | otherwise
   =   mconcatChunk i (drop i xs)
   &&& mconcatSplit i xs 


#else
pmconcatEquivalence :: forall (a :: Symbol). (KnownSymbol a) => Int -> List (Monoid a) -> Proof
{-@ pmconcatEquivalence :: i:Int -> is:List (Monoid a) -> {pmconcat i is == mconcat is} / [llen is] @-}
pmconcatEquivalence _ _ = trivial     
#endif

