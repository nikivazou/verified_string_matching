{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE IncoherentInstances   #-}
module Language.Haskell.Liquid.ProofCombinators (

    (==:), (<=:), (<:), (>:)

  , (==?)

  , (==.), (<=.), (<.), (>.), (>=.)

  , (?), (***)

  , (==>), (&&&), (∵)

  , proof, toProof, simpleProof, trivial 

  , QED(..)

  , Proof

  , byTheorem, castWithTheorem, cast 

  , lemma, lemmata, byLemma, byLemmata

  ) where

infixl 3 `byLemma`
infixl 3 `byLemmata`

{-@ lemma :: Proof -> a -> a @-}
lemma :: Proof -> a -> a 
lemma _ x = x 

{-@ lemmata :: [Proof] -> a -> a @-}
lemmata :: [Proof] -> a -> a 
lemmata _ x = x 

{-@ byLemma :: a -> Int -> a @-}
byLemma :: a -> Int -> a 
byLemma x _ = x 
{-@ byLemmata :: a -> [Int] -> a @-}
byLemmata :: a -> [Int] -> a 
byLemmata x _ = x 
type Proof = ()

trivial :: Proof
trivial = ()


data QED = QED

infixl 2 ***

(***) :: a -> QED -> Proof
_ *** _ = ()


-- | Because provide lemmata ? or ∵

infixl 3 ∵

(∵) :: (Proof -> a) -> Proof -> a
f ∵ y = f y


infixl 3 ?

(?) :: (Proof -> a) -> Proof -> a
f ? y = f y



{-@ measure proofBool :: Proof -> Bool @-}

-- | Proof combinators (are Proofean combinators)
{-@ (==>) :: p:Proof
          -> q:Proof
          -> {v:Proof |
          ((Prop (proofBool p)) && (Prop (proofBool p) => Prop (proofBool q)))
          =>
          ((Prop (proofBool p) && Prop (proofBool q)))
          } @-}
(==>) :: Proof -> Proof -> Proof
p ==> q = ()


{- (&&&) :: p:{Proof | Prop (proofBool p) }
          -> q:{Proof | Prop (proofBool q) }
          -> {v:Proof | Prop (proofBool p) && Prop (proofBool q) } @-}
(&&&) :: Proof -> Proof -> Proof
p &&& q = ()


-- | proof goes from Int to resolve types for the optional proof combinators
proof :: Int -> Proof
proof _ = ()

toProof :: a -> Proof
toProof _ = ()

simpleProof :: Proof
simpleProof = ()

-- | proof operators requiring proof terms
infixl 3 ==:, <=:, <:, >:, ==?


-- | Comparison operators requiring proof terms

(<=:) :: a -> a -> Proof -> a
{-@ (<=:) :: x:a -> y:a -> {v:Proof | x <= y } -> {v:a | v == x } @-}
(<=:) x y _ = x

(<:) :: a -> a -> Proof -> a
{-@ (<:) :: x:a -> y:a -> {v:Proof | x < y } -> {v:a | v == x } @-}
(<:) x y _ = x


(>:) :: a -> a -> Proof -> a
{-@ (>:) :: x:a -> y:a -> {v:Proof | x >y } -> {v:a | v == x } @-}
(>:) x _ _ = x


(==:) :: a -> a -> Proof -> a
{-@ (==:) :: x:a -> y:a -> {v:Proof| x == y} -> {v:a | v == x && v == y } @-}
(==:) x _ _ = x


-- | proof operators with optional proof terms
infixl 3 ==., <=., <., >., >=.


-- | Comparison operators requiring proof terms optionally

class ToProve a r where
  (==?) :: a -> a -> r


class OptEq a r where
  (==.) :: a -> a -> r

instance (a~b) => OptEq a (Proof -> b) where
{-@ instance OptEq a (Proof -> b) where
  ==. :: x:a -> y:a -> {v:Proof | x == y} -> {v:b | v ~~ x && v ~~ y}
  @-}
  (==.) x _ _ = x

instance (a~b) => OptEq a b where
{-@ instance OptEq a b where
  ==. :: x:a -> y:{a| x == y} -> {v:b | v ~~ x && v ~~ y }
  @-}
  (==.) x _ = x


class OptLEq a r where
  (<=.) :: a -> a -> r


instance (a~b) => OptLEq a (Proof -> b) where
{-@ instance OptLEq a (Proof -> b) where
  <=. :: x:a -> y:a -> {v:Proof | x <= y} -> {v:b | v ~~ x }
  @-}
  (<=.) x _ _ = x

instance (a~b) => OptLEq a b where
{-@ instance OptLEq a b where
  <=. :: x:a -> y:{a | x <= y} -> {v:b | v ~~ x }
  @-}
  (<=.) x _ = x

class OptGEq a r where
  (>=.) :: a -> a -> r

instance OptGEq a (Proof -> a) where
{-@ instance OptGEq a (Proof -> a) where
  >=. :: x:a -> y:a -> {v:Proof| x >= y} -> {v:a | v == x }
  @-}
  (>=.) x _ _ = x

instance OptGEq a a where
{-@ instance OptGEq a a where
  >=. :: x:a -> y:{a| x >= y} -> {v:a | v == x  }
  @-}
  (>=.) x _ = x


class OptLess a r where
  (<.) :: a -> a -> r

instance (a~b) => OptLess a (Proof -> b) where
{-@ instance OptLess a (Proof -> b) where
  <. :: x:a -> y:a -> {v:Proof | x < y} -> {v:b | v ~~ x  }
  @-}
  (<.) x _ _ = x

instance (a~b) => OptLess a b where
{-@ instance OptLess a b where
  <. :: x:a -> y:{a| x < y} -> {v:b | v ~~ x  }
  @-}
  (<.) x _ = x


class OptGt a r where
  (>.) :: a -> a -> r

instance (a~b) => OptGt a (Proof -> b) where
{-@ instance OptGt a (Proof -> b) where
  >. :: x:a -> y:a -> {v:Proof| x > y} -> {v:b | v ~~ x }
  @-}
  (>.) x _ _ = x

instance (a~b) => OptGt a b where
{-@ instance OptGt a b where
  >. :: x:a -> y:{a| x > y} -> {v:b | v ~~ x  }
  @-}
  (>.) x y = x


-------------------------------------------------------------------------------
----------  Casting -----------------------------------------------------------
-------------------------------------------------------------------------------

{-@ measure castWithTheorem :: a -> b -> b @-}
castWithTheorem :: a -> b -> b 
castWithTheorem _ x = x 


{-@ measure cast :: b -> a -> a @-}
{-@ cast :: b -> x:a -> {v:a | v == x } @-}
cast :: b -> a -> a 
cast _ x = x 


byTheorem :: a -> Proof -> a
byTheorem a _ = a

