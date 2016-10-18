{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE CPP #-}

{-@ LIQUID "--cores=10"            @-}
{-@ LIQUID "--higherorder"         @-}
{-@ LIQUID "--totality"            @-}
{-@ LIQUID "--exactdc"             @-}
{-@ LIQUID "--no-measure-fields"   @-}

module Main where

import qualified Prelude 

import Prelude hiding ( mempty, mappend, id, mconcat, map, (++), (<>)
                      , take, drop  
                      , error
                      )


import Data.String hiding (fromString)
import GHC.TypeLits
import Data.Maybe 

import String
import Language.Haskell.Liquid.ProofCombinators 

import Data.Proxy 


#include "Internal.hs"

{-@ infix <> @-}
{-@ infix <+> @-}

{-@ symbolVal :: forall n proxy. KnownSymbol n => x:proxy n 
  -> {v:String | v == n && v == symbolVal x } @-}
{-@ measure symbolVal :: p n -> String @-}


-------------------------------------------------------------------------------
----------  Indexing Structure Definition -------------------------------------
-------------------------------------------------------------------------------

data SM (target :: Symbol) where 
  SM :: RString       -- | input string
     -> (List Int)      -- | valid indices of target in input
     -> SM target
  deriving (Show)

{-@ data SM target 
  = SM { input   :: RString
       , indices :: List (GoodIndex input target)
       } @-}

{-@ type GoodIndex Input Target 
  = {i:Int | IsGoodIndex Input Target i }
  @-}

{-@ type GoodIndexTwo Input X Target 
  = {i:Int | (IsGoodIndex Input Target i)  && (IsGoodIndex (Input <+> X) Target i) }
  @-}


{-@ predicate IsGoodIndex Input Target I
  =  (subString Input I (stringLen Target)  == Target)
  && (I + stringLen Target <= stringLen Input)
  && (0 <= I)
  @-}

-------------------------------------------------------------------------------
----------  Monoid Operators on SM --------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect ε @-}
ε :: forall (target :: Symbol). (KnownSymbol target) =>  SM target
ε = SM stringEmp N


{-@ reflect <> @-}
(<>) :: forall (target :: Symbol).  (KnownSymbol target) => SM target -> SM target -> SM target
(SM i1 is1) <> (SM i2 is2)
  = SM (i1 <+> i2) (is1' ++ is ++ is2')
  where 
    tg   = fromString (symbolVal (Proxy :: Proxy target))
    is1' = map (castGoodIndexRight tg i1 i2) is1
    is   = makeNewIndices i1 i2 tg
    is2' = map (shiftStringRight tg i1 i2)   is2

-- | Helpers 
{-@ reflect shiftStringRight @-}
shiftStringRight :: RString -> RString -> RString -> Int -> Int 
{-@ shiftStringRight :: target:RString -> left:RString -> right:RString -> i:GoodIndex right target 
  -> {v:(GoodIndex {left <+> right} target) | v == i + stringLen left } @-}
shiftStringRight target left right i 
  = cast (subStringConcatFront right left (stringLen target) i) (shift (stringLen left) i)

{-@ reflect makeNewIndices @-}
{-@ makeNewIndices :: s1:RString -> s2:RString -> target:RString -> List (GoodIndex {s1 <+> s2} target) @-}
makeNewIndices :: RString -> RString -> RString -> List Int 
makeNewIndices s1 s2 target
  | stringLen target < 2 
  = N
  | otherwise
  = makeIndices (s1 <+> s2) target
                (maxInt (stringLen s1 - (stringLen target-1)) 0)
                (stringLen s1 - 1)

{-@ reflect maxInt @-}
maxInt :: Int -> Int -> Int 
maxInt x y = if x <= y then y else x 

{-@ reflect shift @-}
shift :: Int -> Int -> Int 
shift x y = x + y 

-- | Casting good indices: the below operators are liquid casts and behave like id at runtime


{-@ reflect castGoodIndexRight @-}
castGoodIndexRight :: RString -> RString -> RString -> Int -> Int  
{-@ castGoodIndexRight :: target:RString -> input:RString -> x:RString -> i:GoodIndex input target 
   -> {v:(GoodIndexTwo input x target)| v == i} @-}
castGoodIndexRight target input x i  = cast (subStringConcatBack input x (stringLen target) i) i



-------------------------------------------------------------------------------
----------  Indices' Generation -----------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect makeIndices @-}
makeIndices :: RString -> RString -> Int -> Int -> List Int 
{-@ makeIndices :: input:RString -> target:RString -> lo:Nat -> hi:Int -> List (GoodIndex input target) 
  / [hi - lo + 1] @-}
makeIndices input target lo hi 
  | hi < lo 
  = N
makeIndices input target lo hi 
  | isGoodIndex input target lo
  = lo `C` rest
  | otherwise 
  = rest    
  where
    rest = makeIndices input target (lo + 1) hi 
 
{-@ reflect isGoodIndex @-}
isGoodIndex :: RString -> RString -> Int -> Bool 
{-@ isGoodIndex :: input:RString -> target:RString -> i:Int 
  -> {b:Bool | Prop b <=> IsGoodIndex input target i} @-}
isGoodIndex input target i 
  =  subString input i (stringLen target)  == target  
  && i + stringLen target <= stringLen input
  && 0 <= i    


-------------------------------------------------------------------------------
----------  List Structure ----------------------------------------------------
-------------------------------------------------------------------------------
   
data List a = N | C a (List a) deriving (Eq, Functor, Foldable, Traversable)
{-@ data List [llen] a 
  = N | C {lhead :: a , ltail :: List a} @-}

instance Show a => Show (List a) where
  show xs = "[" Prelude.++ go xs Prelude.++ "]"
    where
      go N = ""
      go (C x N)  = show x 
      go (C x xs) = show x Prelude.++ ", " Prelude.++ go xs  

{-@ measure llen @-}
{-@ llen :: List a -> Nat @-} 
llen :: List a -> Int 
llen N        = 0 
llen (C _ xs) = 1 + llen xs 

{-@ reflect map @-}
{-@ map :: (a -> b) -> is:List a -> {os:List b | llen is == llen os} @-}
map :: (a -> b) -> List a -> List b
map _ N        = N
map f (C x xs) = C (f x) (map f xs)

{-@ infix ++ @-}

{-@ reflect ++ @-}
(++) :: List a -> List a -> List a 
(++) N        ys = ys 
(++) (C x xs) ys = x `C` (xs ++ ys)

{-@ type Pos = {v:Int | 0 < v } @-}




-------------------------------------------------------------------------------
----------  Proof that SM is a Monoid -----------------------------------------
-------------------------------------------------------------------------------



εLeft :: forall (t :: Symbol). (KnownSymbol t) => SM t -> Proof
{-@ εLeft :: xs:SM t -> { xs <> ε == xs } @-}
εLeft (SM i is) 
  =   SM i is <> (ε :: SM t)
  ==. SM i is <> (SM stringEmp N) 
  ==. SM (i <+> stringEmp) 
          (is1 ++ isNew ++ is2)
       ? concatStringNeutralLeft i
  ==. SM i (is ++ N ++ N)
       ? (mapCastId tg i stringEmp is &&& makeNewIndicesNullLeft i tg)
  ==. SM i is 
       ? (appendNil is) 
  *** QED 
  where
    tg    = fromString (symbolVal (Proxy :: Proxy t))
    is1   = map (castGoodIndexRight tg i stringEmp) is
    isNew = makeNewIndices i stringEmp tg
    is2   = map (shiftStringRight tg i stringEmp) N




εRight :: forall (t :: Symbol). (KnownSymbol t) => SM t -> Proof
{-@ εRight :: xs:SM t -> {ε <> xs == xs } @-}
εRight (SM i is)
  =   (ε :: SM t) <> (SM i is) 
  ==. (SM stringEmp N) <> (SM i is) 
  ==. SM (stringEmp <+> i) (is1 ++ isNew ++ is2)
       ? concatStringNeutralRight i
  ==. SM i (N ++ N ++ is)
       ? (mapShiftZero tg i is &&& makeNewIndicesNullRight i tg)
  ==. SM i is 
  *** QED 
  where
    tg    = fromString (symbolVal (Proxy :: Proxy t)) 
    is1   = map (castGoodIndexRight tg i stringEmp) N
    isNew = makeNewIndices stringEmp i tg 
    is2   = (map (shiftStringRight tg stringEmp i) is)


{-@ mapShiftZero :: target:RString -> i:RString -> is:List (GoodIndex i target) 
  -> {map (shiftStringRight target stringEmp i) is == is } 
  / [llen is] @-}
mapShiftZero target i N
  =   map (shiftStringRight target stringEmp i) N ==. N *** QED  
mapShiftZero target i (C x xs)
  =   map (shiftStringRight target stringEmp i) (C x xs) 
  ==. shiftStringRight target stringEmp i x `C` map (shiftStringRight target stringEmp i) xs
  ==. shift (stringLen stringEmp) x `C` map (shiftStringRight target stringEmp i) xs
  ==. shift 0 x `C` map (shiftStringRight target stringEmp i) xs
  ==. x `C` map (shiftStringRight target stringEmp i) xs
  ==. x `C` xs ? mapShiftZero target i xs 
  *** QED 
-------------------------------------------------------------------------------
----------  Lemmata on Lists --------------------------------------------------
-------------------------------------------------------------------------------

{-@ appendNil :: xs:List a -> { xs ++ N = xs } @-} 
appendNil :: List a -> Proof 
appendNil N 
  =   N ++  N
  ==. N
  *** QED 
appendNil (C x xs) 
  =   C x xs ++  N
  ==. C x (xs ++  N)
  ==. C x xs ? appendNil xs 
  *** QED 




-------------------------------------------------------------------------------
----------  Lemmata on Empty Indices ------------------------------------------
-------------------------------------------------------------------------------


makeNewIndicesNullLeft :: RString -> RString -> Proof 
{-@ makeNewIndicesNullLeft 
  :: s:RString 
  -> t:RString 
  -> {makeNewIndices s stringEmp t == N } @-} 

makeNewIndicesNullLeft s t = undefined   
    

makeNewIndicesNullRight :: RString -> RString -> Proof 
{-@ makeNewIndicesNullRight 
  :: s1:RString 
  -> t:RString 
  -> {makeNewIndices stringEmp s1 t == N } @-} 
makeNewIndicesNullRight s t 
  | stringLen t < 2 
  = makeNewIndices stringEmp s t  ==. N *** QED 
  | otherwise
  =   makeNewIndices stringEmp s t
  ==. makeIndices (stringEmp <+> s) t
                   (maxInt (1 + stringLen stringEmp - stringLen t) 0)
                   (stringLen stringEmp - 1)
  ==. makeIndices s t
                   (maxInt (1 - stringLen t) 0)
                   (-1)
      ? concatStringNeutralRight s 
  ==. makeIndices s t 0 (-1)
  ==. N  
  *** QED

-------------------------------------------------------------------------------
----------  Casting Lemmata  --------------------------------------------------
-------------------------------------------------------------------------------



mapCastId :: RString -> RString -> RString -> List Int -> Proof 
{-@ mapCastId :: tg:RString -> x:RString -> y:RString -> is:List (GoodIndex x tg) -> 
      {map (castGoodIndexRight tg x y) is == is} @-}
mapCastId tg x y N 
  = map (castGoodIndexRight tg x y) N ==. N *** QED 
mapCastId tg x y (C i is) 
  =   map (castGoodIndexRight tg x y) (C i is) 
  ==. castGoodIndexRight tg x y i `C` map (castGoodIndexRight tg x y) is 
  ==. i `C` is 
       ? mapCastId tg x y is  
  *** QED 
