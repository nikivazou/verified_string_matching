{-# LANGUAGE CPP                  #-}
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
{-@ LIQUID "--trust-internals"     @-}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}


{-@ infix <+> @-}
{-@ infix <> @-}

import Language.Haskell.Liquid.ProofCombinators 



import Prelude hiding ( mempty, mappend, mconcat, map, Monoid
                      , take, drop  
                      , error, undefined
                      )


#include "../Data/List/RList.hs"

#endif

{-@ automatic-instances listRightId @-}
{-@ automatic-instances listLeftId  @-}
{-@ automatic-instances listAssoc   @-}

{-@ listRightId :: xs:List a -> { append N xs = xs } @-} 
listRightId :: List a -> Proof 
listRightId xs = trivial

{-@ listLeftId :: xs:List a -> { append xs N = xs } @-} 
listLeftId :: List a -> Proof 
listLeftId N        = trivial 
listLeftId (C _ xs) = listLeftId xs 


{-@ listAssoc :: x:List a -> y:List a -> z:List a 
     -> {(append x (append y z)) == (append (append x y) z) } @-}
listAssoc :: List a -> List a -> List a -> Proof
listAssoc N _ _       = trivial
listAssoc (C _ x) y z = listAssoc x y z


{-@ automatic-instances listTakeDrop   @-}

{-@ listTakeDrop :: i:{Int | 0 <= i} -> xs:{List a | i <= llen xs}  -> {xs == append (take i xs) (drop i xs)} @-}
listTakeDrop :: Int -> List a -> Proof 
listTakeDrop i N           
  = append (take i N) (drop i N) ==. append N N ==. N *** QED  
listTakeDrop i (C x xs) 
  | i == 0 
  = append (take i (C x xs)) (drop i (C x xs))
  ==. append N (C x xs)
  ==. C x xs
  *** QED 
listTakeDrop i (C x xs) 
  =   append (take i (C x xs))     (drop i (C x xs))
  ==. append (C x (take (i-1) xs)) (drop (i-1) xs)
  ==. C x (append (take (i-1) xs)  (drop (i-1) xs))
      ? listTakeDrop (i-1) xs    
  ==. C x xs 
  *** QED 

-------------------------------------------------------------------------------
--------------  Compatibility with the old names  -----------------------------
-------------------------------------------------------------------------------


{-@ appendNil :: xs:List a -> { append xs N = xs } @-} 
appendNil :: List a -> Proof 
appendNil = listLeftId 


{-@ appendAssoc :: x:List a -> y:List a -> z:List a 
     -> {(append x (append y z)) == (append (append x y) z) } @-}
appendAssoc :: List a -> List a -> List a -> Proof
appendAssoc = listAssoc


