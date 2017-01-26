{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE MultiParamTypeClasses   #-}


{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--exactdc"         @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--trust-internals" @-}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}

module Test where

import Language.Haskell.Liquid.ProofCombinators
import Parallelize 


import Prelude hiding (sum, Monoid(..), map)

{-@ axiomatize idList @-}
idList :: List Int -> List Int 
idList Nil         = Nil 
idList (Cons x xs) = Cons x (idList xs)



{-@ morphismProof :: x:List Int -> y:List Int 
  -> {v:Proof |  idList (mappendList x y) == mappendList (idList x) (idList y) } @-}
morphismProof :: Morphism (List Int) (List Int) 
morphismProof Nil y 
  =   idList (mappendList Nil y) 
  ==. idList y 
  ==. mappendList Nil (idList y) ? leftIdList (idList y) 
  ==. mappendList (idList Nil) (idList y)
  *** QED 


morphismProof (Cons x xs) ys 
  =   idList (mappendList (Cons x xs) ys) 
  ==. idList (Cons x (mappendList xs ys))
  ==. Cons x (idList (mappendList xs ys))
  ==. Cons x (mappendList (idList xs) (idList ys))
       ? morphismProof xs ys 
  ==. mappendList (Cons x (idList xs)) (idList ys)
  ==. mappendList (idList (Cons x xs)) (idList ys)
  *** QED 


{-@ psum :: {v:Int | 0 <= v} -> xs:List Int -> {v:List Int | v == idList xs} @-}
psum :: Int -> List Int -> List Int 
psum i = parallelize idList (\x y -> (morphismProof x y &&& morphismProof' x y)) i i 



{-@ assume morphismProof' :: x:List Int -> y:List Int 
  -> {(idList (mappendList x y) == mappendList (idList x) (idList y)) => (idList (mappend x y) == mappend (idList x) (idList y)) } @-}
morphismProof' :: Morphism (List Int) (List Int) 
morphismProof' _ _ = trivial


instance (Eq a) => Parallelizable (List a) (List a) where


instance ChunkableMonoid (List a) where
  length = lenList 
  drop   = dropList
  take   = takeList 

  takeDropProp i x = takeDropPropList i x &&& takeDropPropListAssumed i x

{-@ assume takeDropPropListAssumed :: i:Nat -> x:List a -> { mappendList (takeList i x) (dropList i x) == mappend (takeList i x) (dropList i x) } @-}
takeDropPropListAssumed :: Nat -> List a -> Proof 
takeDropPropListAssumed _ _ = trivial


{-@ axiomatize takeList @-}
{-@ takeList   :: i:{Int | 0 <= i} -> x:{ List a | i <= length x} -> {v: List a | length v == i } @-}
takeList :: Nat -> List a -> List a 
takeList i xs       | i == 0 =  Nil 
takeList i (Cons x xs) = Cons x (takeList (i-1) xs)

{-@ axiomatize dropList @-}
{-@ dropList   :: i:Nat -> x:{ List a | i <= length x} -> {v: List a | length v == length x - i } @-}
dropList :: Nat -> List a -> List a 
dropList i xs       | i == 0 =  xs 
dropList i (Cons x xs) = dropList (i-1) xs


{-@ takeDropPropList :: i:Nat -> xs:{List a | i <= length xs}  -> {xs == mappendList (takeList i xs) (dropList i xs)} / [length xs] @-}
takeDropPropList :: Nat -> List a -> Proof 
takeDropPropList = undefined 

instance Monoid (List a) where
  mempty  = memptyList 
  mappend = mappendList 

  leftId  = leftIdList 
  rightId = rightIdList 
  assoc   = assocList 


{-@ axiomatize memptyList @-}
memptyList :: List a 
memptyList = Nil  

{-@ axiomatize mappendList @-}
mappendList :: List a -> List a -> List a 
mappendList Nil ys        = ys 
mappendList (Cons x xs) ys = Cons x (mappendList xs ys)

{-@ automatic-instances leftIdList @-}
{-@ leftIdList :: x:List a -> {mappendList memptyList x = x} @-}
leftIdList :: List a -> Proof 
leftIdList x = trivial 

{-@ automatic-instances rightIdList @-}
{-@ rightIdList :: x:List a -> {mappendList x memptyList = x} @-}
rightIdList :: List a -> Proof 
rightIdList Nil = trivial
rightIdList (Cons _ xs) = rightIdList xs 


{-@ automatic-instances assocList @-}
{-@ assocList :: x:List a -> y:List a -> z:List a -> {mappendList x (mappendList y z) = mappendList (mappendList x y) z} @-}
assocList :: List a -> List a -> List a -> Proof 
assocList Nil _ _ = trivial
assocList (Cons _ xs) ys zs = assocList xs ys zs


data List a = Nil | Cons a (List a) deriving (Eq)
{-@ data List [lenList ] a = Nil | Cons {listHead :: a, listTail :: List a} @-}
{-@ invariant {v:List a | length v == lenList v} @-}



{-@ axiomatize map @-}
{-@ map :: (a -> b) -> xs:List a -> {v:List b | lenList v == lenList xs} @-} 
map :: (a -> b) -> List a -> List b 
map _ Nil         = Nil
map f (Cons x xs) = Cons (f x) (map f xs)



{-@ measure lenList @-}
{-@ lenList :: List a -> Nat @-}
lenList :: List a -> Int 
lenList Nil = 0 
lenList (Cons _ xs) = 1 + lenList xs 



type Nat          = Int 
{-@ type Nat      = {v:Int | 0 <= v} @-}



-------------------------------------------------------------------------------
-------------  Liquid HACKS ---------------------------------------------------
-------------------------------------------------------------------------------

-- THIS needs to be here due to name resolution

{-@ measure lengthList :: a -> Int @-}


-- THIS WILL BE AUTO GENERATED

{-@ instance Monoid (List a) where 
  assume mempty  :: {v:List a | (v = memptyList) };
  assume mappend :: {v:(x:List a -> y:List a -> List a) | (v == mappendList)};
  leftId  :: x:List a -> {v:Proof | mappendList memptyList x = x } ;
  rightId :: x:List a -> {v:Proof | mappendList x memptyList = x } ;
  assoc   :: x:List a -> y:List a -> z:List a-> {v:Proof | mappendList x (mappendList y z) = mappendList (mappendList x y) z}
  @-}

