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

