{-@ appendNil :: xs:List a -> { append xs N = xs } @-} 
appendNil :: List a -> Proof 
appendNil N 
  =   append N N
  ==. N
  *** QED 
appendNil (C x xs) 
  =   append (C x xs) N
  ==. C x (append xs N)
  ==. C x xs ? appendNil xs 
  *** QED 


{-@ appendAssoc :: x:List a -> y:List a -> z:List a 
     -> {(append x (append y z)) == (append (append x y) z) } @-}
appendAssoc :: List a -> List a -> List a -> Proof
appendAssoc N y z 
  =   append N (append y z)
  ==. append y z
  ==. append (append N y) z
  *** QED 
appendAssoc (C x xs) y z
  =   append (C x xs) (append y z) 
  ==. C x (append xs (append y z))
  ==. C x (append (append xs y) z)
        ? appendAssoc xs y z
  ==. append (C x (append xs y)) z
  ==. append (append (C x xs) y) z
  *** QED 
  