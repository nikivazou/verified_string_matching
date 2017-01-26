{-@ listRightId :: xs:List a -> { append N xs = xs } @-} 
listRightId :: List a -> Proof 
listRightId xs = append N xs ==. xs *** QED 

{-@ listLeftId :: xs:List a -> { append xs N = xs } @-} 
listLeftId :: List a -> Proof 
listLeftId N 
  =   append N N
  ==. N
  *** QED 
listLeftId (C x xs) 
  =   append (C x xs) N
  ==. C x (append xs N)
  ==. C x xs ? listLeftId xs 
  *** QED 


{-@ listAssoc :: x:List a -> y:List a -> z:List a 
     -> {(append x (append y z)) == (append (append x y) z) } @-}
listAssoc :: List a -> List a -> List a -> Proof
listAssoc N y z 
  =   append N (append y z)
  ==. append y z
  ==. append (append N y) z
  *** QED 
listAssoc (C x xs) y z
  =   append (C x xs) (append y z) 
  ==. C x (append xs (append y z))
  ==. C x (append (append xs y) z)
        ? listAssoc xs y z
  ==. append (C x (append xs y)) z
  ==. append (append (C x xs) y) z
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

