{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE CPP                   #-}
{-# LANGUAGE ScopedTypeVariables   #-}

{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--exactdc"         @-}
{-@ LIQUID "--totality"        @-}

{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}

{-@ assume withStrategy :: _ -> x:a -> {v:a | v == x } @-}

module Parallelize (

  Parallelizable(..), Monoid(..), ChunkableMonoid(..), 

  Morphism

  ) where 

import Prelude hiding (Monoid (..), length, drop, take, map)

import Language.Haskell.Liquid.ProofCombinators

import Control.Parallel.Strategies 

#include "Proofs/Equivalence.hs"
#include "Proofs/Lists.hs"



class (ChunkableMonoid m, ChunkableMonoid n, Eq m) => Parallelizable n m where 

  parallelize :: (n -> m) -> Morphism n m -> Nat -> Nat -> n -> m 
  parallelize f p i j x = parallelizeWithStrategy parStrategy f p i j x
                            `byTheorem` equivalencePropDef parStrategy f p i j x

  parallelizeWithStrategy :: Strategy (L m) -> (n -> m) -> Morphism n m -> Nat -> Nat -> n -> m 
  parallelizeWithStrategy stg f p i j x = parallelizeWithStrategyDef  stg f p i j x 
                            `byTheorem` equivalencePropDef stg f p i j x




{-@ class Parallelizable n m where 
  parallelize             :: f:(n -> m) -> Morphism n m f -> Nat -> Nat -> x:n -> {v:m | v = f x }

  parallelizeWithStrategy :: Strategy (L m) -> f:(n -> m) -> Morphism n m f -> Nat -> Nat -> x:n -> {v:m | v == f x} 

  @-}



{-@ axiomatize parallelizeWithStrategyDef @-}
parallelizeWithStrategyDef :: (ChunkableMonoid n, Monoid m) => Strategy (L m) -> (n -> m) -> Morphism n m -> Nat -> Nat -> n -> m 
-- NV TODO NAME RESOLTUION BUG the first argument's name should be xa4....
{-@ parallelizeWithStrategyDef :: Strategy (L m) -> xa4:(n -> m) -> Morphism n m xa4 -> Nat -> Nat -> n -> m @-}
parallelizeWithStrategyDef stg f p i j x 
  | i == 0 
  = f x 
  | otherwise 
  = pmconcatWithStrategy stg j (pmapWithStrategy stg f (chunk i x)) 

-------------------------------------------------------------------------------
------------- Helper Type Definitiions  ---------------------------------------
-------------------------------------------------------------------------------


type Morphism n m = n -> n -> Proof  
{-@ type Morphism n m F = x:n -> y:n -> {v:Proof |  F (mappend x y) == mappend (F x) (F y) } @-}

-- NV TODO: restore the following correct type: now fixpoint crashes
{- type Morphism n m F = x:n -> y:n -> {v:Proof | F mempty = mempty && F (mappend x y) == mappend (F x) (F y) } @-}

type Pos          = Int 
{-@ type Pos      = {v:Int | 0 < v} @-}

type Nat          = Int 
{-@ type Nat      = {v:Int | 0 <= v} @-}


-------------------------------------------------------------------------------
------------- Verified Monoid -------------------------------------------------
-------------------------------------------------------------------------------

class Monoid m where 
  mempty  :: m 
  mappend :: m -> m -> m 

  leftId  :: m -> Proof 
  rightId :: m -> Proof
  assoc   :: m -> m -> m -> Proof 

{-@ class Monoid m where
    mempty  :: m 
    mappend :: m -> m -> m  
    leftId  :: x:m -> {v:Proof | mappend mempty x = x }
    rightId :: x:m -> {v:Proof | mappend x mempty = x }

    assoc   :: x:m -> y:m -> z:m -> {v:Proof | mappend x (mappend y z) = mappend (mappend x y) z}
  @-}

{-@ reflect method mempty   @-}
{-@ reflect method mappend  @-}

{-@ axiomatize mconcat @-}
mconcat :: Monoid m => L m -> m 
{-@ mconcat :: Monoid m => L m -> m @-}
mconcat N        = mempty
mconcat (C x xs) = x `mappend` mconcat xs 


{-@ axiomatize pmconcatWithStrategy @-}
{-@ pmconcatWithStrategy :: Monoid m => Strategy (L m) -> Int -> xs:L m ->  m / [length xs] @-}
pmconcatWithStrategy :: Monoid m =>  Strategy (L m) -> Int -> L m ->  m
pmconcatWithStrategy stg i x 
  | i <= 1 || length x <= i 
  = mconcat x 
  | otherwise
  = pmconcatWithStrategy stg i (pmapWithStrategy stg mconcat (chunk i x))

{-@ pmconcat :: Monoid m => Int -> xs:L m -> m  @-}
pmconcat :: Monoid m => Int -> L m ->  m
pmconcat = pmconcatWithStrategy parStrategy

-------------------------------------------------------------------------------
------------- Verified Chunkable Monoid ---------------------------------------
-------------------------------------------------------------------------------

class Monoid m => ChunkableMonoid m where 
	length :: m -> Nat 
	drop   :: Nat -> m -> m 
	take   :: Nat -> m -> m 

	takeDropProp :: Nat -> m -> Proof 

{-@ class ChunkableMonoid m where
	length :: x:m -> {v:Int | 0 <= v && v = length x} 
	drop   :: i:{Int | 0 <= i} -> x:{m | i <= length x} -> {v:m | length v == length x - i } 
	take   :: i:{Int | 0 <= i} -> x:{m | i <= length x} -> {v:m | length v == i }

	takeDropProp :: i:{Int | 0 <= i} -> x:{m | i <= length x} -> {v:Proof | x == mappend (take i x) (drop i x)} 
 @-}

{-@ reflect method take   @-}
{-@ reflect method drop   @-}
{-@ reflect method length @-}


{-@ axiomatize chunk @-}
{-@ chunk :: ChunkableMonoid m =>  i:Pos -> x:m 
          -> {v:L m | if (length x <= i) then (length v == 1) else 
          	          (if (i == 1) then (length v == length x) else (length v < length x))}  / [length x] @-}
chunk :: ChunkableMonoid m =>  Pos -> m -> L m  
chunk i x 
  | length x <= i = C x N 
  | otherwise     = take i x `C` chunk i (drop i x)



-------------------------------------------------------------------------------
------------- List Definitions & Instances Verified Chunkable Monoid ----------
-------------------------------------------------------------------------------

data L a = N | C a (L a) deriving (Functor, Foldable, Traversable, Eq)
{-@ data L [lengthList] a = N | C {lhead :: a, ltail :: L a} @-}


{-@ axiomatize map @-}
{-@ map :: (a -> b) -> xs:L a -> {v:L b | length xs == length v}  @-}
map :: (a -> b) -> L a -> L b 
map _ N        = N 
map f (C x xs) = f x `C` map f xs 

instance Monoid (L a) where
  mempty  = memptyList 
  mappend = mappendList 

  leftId  = leftIdList 
  rightId = rightIdList 
  assoc   = assocList 


{-@ axiomatize memptyList @-}
memptyList :: L a 
memptyList = N   

{-@ axiomatize mappendList @-}
mappendList :: L a -> L a -> L a 
mappendList N ys        = ys 
mappendList (C x xs) ys = C x (mappendList xs ys)



instance ChunkableMonoid (L a) where
  length = lengthList 
  take   = takeList 
  drop   = dropList

  takeDropProp i x = takeDropPropList i x &&& takeDropPropListAssumed i x 


{-@ measure lengthList @-}  
{-@ lengthList :: x:L a -> Nat @-}
lengthList :: L a -> Nat 
lengthList N        = 0 
lengthList (C _ xs) = 1 + lengthList xs


{-@ axiomatize takeList @-}
{-@ takeList   :: i:Nat -> x:{ L a | i <= length x} -> {v: L a | length v == i } @-}
takeList :: Nat -> L a -> L a 
takeList i xs       | i == 0 =  N 
takeList i (C x xs) = C x (takeList (i-1) xs)

{-@ axiomatize dropList @-}
{-@ dropList   :: i:Nat -> x:{ L a | i <= length x} -> {v: L a | length v == length x - i } @-}
dropList :: Nat -> L a -> L a 
dropList i xs       | i == 0 =  xs 
dropList i (C x xs) = dropList (i-1) xs


-------------------------------------------------------------------------------
------------- List Parallelization --------------------------------------------
-------------------------------------------------------------------------------

{-@ axiomatize pmapWithStrategy @-}
{-@ pmapWithStrategy :: Strategy (L b) -> (a -> b) -> xs:L a -> {v:L b | length xs == length v } @-}
pmapWithStrategy :: Strategy (L b) -> (a -> b) -> L a -> L b 
pmapWithStrategy stg f xs = withStrategy stg (map f xs)

{-@ parStrategy :: Strategy (L a) @-}
parStrategy :: Strategy (L a)
parStrategy = parTraversable rseq


{-@ axiomatize pmap @-}
{-@ pmap :: (a -> b) -> xs:L a -> {v:L b | length xs == length v } @-}
pmap :: (a -> b) -> L a -> L b 
pmap f xs = withStrategy parStrategy (map f xs)



-------------------------------------------------------------------------------
------------- LIQUID HACKS ----------------------------------------------------
-------------------------------------------------------------------------------

-- | NV TODO: The following should get auto generated

{-@ assume equivalencePropDefAssumed :: stg:Strategy (L m) -> f:(n -> m) -> p:Morphism n m f -> i:Nat -> j:Nat -> x:n -> {v:Proof | parallelizeWithStrategy stg f p i j x == parallelizeWithStrategyDef stg f p i j x } @-}
equivalencePropDefAssumed :: Strategy (L m) -> (n -> m) -> Morphism n m -> Nat -> Nat -> n -> Proof 
equivalencePropDefAssumed _ _ _ _ _ _ = trivial


{-@ assume takeDropPropListAssumed :: i:Nat -> x:L a -> { mappendList (takeList i x) (dropList i x) == mappend (takeList i x) (dropList i x) } @-}
takeDropPropListAssumed :: Nat -> L a -> Proof 
takeDropPropListAssumed _ _ = trivial 

takeListAssumed :: Nat -> L a -> Proof
{-@ assume takeListAssumed :: i:Nat -> x:L a -> { take i x == takeList i x } @-}
takeListAssumed _ _ = trivial 

dropListAssumed :: Nat -> L a -> Proof
{-@ assume dropListAssumed :: i:Nat -> x:L a -> { drop i x == dropList i x } @-}
dropListAssumed _ _ = trivial 


{-@ assume mempty :: {v:m | v == mempty  && v == Parallelize.mempty##rTq } @-}

{-@ invariant {v:L a | length v == lengthList v} @-}

{-@ measure mappend :: a -> a -> a @-}
{-@ measure mempty  :: a @-}
{-@ measure Parallelize.mempty##rTq  :: a @-}
{-@ define Parallelize.mempty##rTq  = mempty  @-}

{-@ measure length :: m -> Int @-}
{-@ measure drop   :: Int -> m -> m @-}
{-@ measure take   :: Int -> m -> m @-}


{-@ measure parallelizeWithStrategy ::  Strategy (L m) -> (n -> m) -> (n -> n -> Proof) -> Int -> Int -> n -> m @-}
