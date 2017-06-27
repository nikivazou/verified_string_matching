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
#define MainCall

#include "../Data/List/RList.hs"
#include "../Data/RString/Chunk.hs"
#include "../Data/List/MList.hs"
#include "../Data/Monoid/PMonoid.hs"
#include "../Proofs/ListMonoidLemmata.hs"
#endif


#ifdef IncludeddistributeInput
#else  
#include "../Proofs/DistributeInput.hs"
#endif
IncludeddistributeInput

{-@ parallelismEquivalence :: 
      f:(RString -> Monoid target) 
   -> (x1:RString -> x2:RString -> {f (x1 <+> x2) ==  (f x1) <> (f x2)})
   -> is:RString  -> n:Integer -> m:Integer
   -> {f is == pmconcat m (map f (chunkString n is)) } @-}

parallelismEquivalence :: forall (target :: Symbol). (KnownSymbol target) 
  => (RString -> Monoid target)
  -> (RString -> RString -> Proof) 
  -> RString -> Integer -> Integer -> Proof
parallelismEquivalence f thm is n m  
  =   pmconcat m (map f (chunkString n is))
  ==. mconcat (map f (chunkString n is))
      ? pmconcatEquivalence m (map f (chunkString n is) :: List (Monoid target))
  ==. f is 
      ? distributeInput f thm is n 
  *** QED  



pmconcatEquivalence :: forall (a :: Symbol). (KnownSymbol a) => Integer -> List (Monoid a) -> Proof
{-@ pmconcatEquivalence :: i:Integer -> is:List (Monoid a) -> {pmconcat i is == mconcat is} / [llen is] @-}

#ifdef CheckParEquivalence


pmconcatEquivalence i is 
  | i <= 1
  = pmconcat i is ==. mconcat is *** QED 
pmconcatEquivalence i N 
  =   pmconcat i N 
  ==. (mempty :: Monoid a) 
  ==. mconcat N 
  *** QED 
pmconcatEquivalence i (C x N) 
  =   pmconcat i (C x N)
  ==. x 
  ==. x <> mempty 
      ? mempty_left x
  ==. x <> mconcat N 
  ==. mconcat (C x N) 
  *** QED 
pmconcatEquivalence i xs 
  | llen xs <= i 
  =   pmconcat i xs 
  ==. pmconcat i (map mconcat (chunk i xs))
  ==. pmconcat i (map mconcat (C xs N))
  ==. pmconcat i (mconcat xs `C` map mconcat N)
  ==. pmconcat i (mconcat xs `C` N)
  ==. mconcat xs
  *** QED 
pmconcatEquivalence i xs
  =   pmconcat i xs 
  ==. pmconcat i (map mconcat (chunk i xs))
  ==. mconcat (map mconcat (chunk i xs))
       ? pmconcatEquivalence i (map mconcat (chunk i xs))
  ==. mconcat xs
       ? mconcatChunk i xs
  *** QED 

-- | Monoid implications 

mconcatSplit :: forall (a :: Symbol). (KnownSymbol a) => Integer -> List (Monoid a) -> Proof 
{-@ mconcatSplit :: i:INat -> xs:{List (Monoid a) | i <= llen xs} 
     -> { mconcat xs ==  mconcat (take i xs) <> mconcat (drop i xs)}
     / [i]
  @-} 
mconcatSplit i N 
  =   mconcat (take i N) <> mconcat (drop i N)
  ==. mconcat N <> mconcat N
  ==. (mempty :: Monoid a) <> (mempty :: Monoid a)
  ==. (mempty :: Monoid a) 
      ? mempty_left  (mempty :: Monoid a)
  ==. mconcat N 
  *** QED 

mconcatSplit i (C x xs)
  | i == 0
  =   mconcat (take i (C x xs)) <> mconcat (drop i (C x xs))
  ==. mconcat N <> mconcat (C x xs)
  ==. mempty <> (mconcat (C x xs))
  ==. mconcat (C x xs)
      ? mempty_right (mconcat (C x xs))
  *** QED 
  | otherwise    
  =    (mconcat (take i (C x xs))) <> (mconcat (drop i (C x xs))) 
  ==.  (mconcat (C x (take (i-1) xs))) <> (mconcat (drop (i-1) xs))
  ==.  ( x <> (mconcat (take (i-1) xs))) <> (mconcat (drop (i-1) xs))
       ? mappend_assoc x (mconcat (take (i-1) xs)) (mconcat (drop (i-1) xs))
  ==.  x <> ((mconcat (take (i-1) xs)) <> (mconcat (drop (i-1) xs)))
       ? mconcatSplit (i-1) xs
  ==. x <> mconcat xs
  ==. mconcat (C x xs)
  *** QED 

-- Generalization to chunking  

mconcatChunk :: forall (a :: Symbol). (KnownSymbol a) => Integer -> List (Monoid a) -> Proof 
{-@ mconcatChunk :: i:Pos -> xs:List (Monoid a) 
  -> { mconcat xs == mconcat (map mconcat (chunk i xs))}
  /  [llen xs] @-}
mconcatChunk i xs  
  | llen xs <= i 
  =   mconcat (map mconcat (chunk i xs))
  ==. mconcat (map mconcat (C xs N))
  ==. mconcat (mconcat xs `C` map mconcat N)
  ==. mconcat (mconcat xs `C` N)
  ==. mconcat xs <> mconcat N
  ==. mconcat xs <> (mempty :: Monoid a)
  ==. mconcat xs 
       ? mempty_left (mconcat xs)
  *** QED  
   | otherwise
   =   mconcat (map mconcat (chunk i xs))
   ==. mconcat (map mconcat (take i xs `C` chunk i (drop i xs)))
   ==. mconcat (mconcat (take i xs) `C` map mconcat (chunk i (drop i xs)))
   ==. (mconcat (take i xs)) <> (mconcat (map mconcat (chunk i (drop i xs))))
   ==. mconcat (take i xs) <> (mconcat (drop i xs))
        ? mconcatChunk i (drop i xs)
   ==. mconcat xs 
        ? mconcatSplit i xs 
   *** QED 


#else
pmconcatEquivalence _ _ = trivial     
#endif

