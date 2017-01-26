data List a = N | C a (List a) 
  deriving (Eq)

#ifdef ParallelEvaluation
-- verification in deriving classes diverges
instance Functor     List where
  fmap f N = N
  fmap f (C x xs) = f x `C` fmap f xs 

instance Foldable    List where

-- GHC bug? default traverse method diverges
instance Traversable List where
   traverse f N = pure N
   traverse f (C x xs) = C <$> f x <*> traverse f xs
#else 
#endif


{-@ data List [llen] a 
  = N | C {lhead :: a , ltail :: List a} @-}

instance Show a => Show (List a) where
  show xs = "[" ++ go xs ++ "]"
    where
      go N = ""
      go (C x N)  = show x 
      go (C x xs) = show x ++ ", " ++ go xs  

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

{-@ axiomatize append @-}
append :: List a -> List a -> List a 
append N        ys = ys 
append (C x xs) ys = x `C` (append xs ys)

{-@ type Pos = {v:Int | 0 < v } @-}

{-@ reflect chunk @-}
{-@ chunk :: i:Pos -> xs:List a -> {v:List (List a) | if (llen xs <= i) then (llen v == 1) else (if (i == 1) then (llen v == llen xs) else (llen v < llen xs)) } / [llen xs] @-}
chunk :: Int -> List a -> List (List a)
chunk i xs 
  | llen xs <= i 
  = C xs N 
  | otherwise
  = C (take i xs) (chunk i (drop i xs))

{-@ reflect drop @-}
{-@ drop :: i:Nat -> xs:{List a | i <= llen xs } -> {v:List a | llen v == llen xs - i } @-} 
drop :: Int -> List a -> List a 
drop i N = N 
drop i (C x xs)
  | i == 0 
  = C x xs  
  | otherwise 
  = drop (i-1) xs 

{-@ reflect take @-}
{-@ take :: i:Nat -> xs:{List a | i <= llen xs } -> {v:List a | llen v == i} @-} 
take :: Int -> List a -> List a 
take i N = N 
take i (C x xs)
  | i == 0 
  = N  
  | otherwise 
  = C x (take (i-1) xs)


  