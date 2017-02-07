#define IncludedListLemmata

{-@ automatic-instances appendGroup @-}

appendGroup :: List a -> List a -> List a -> List a -> List a -> Proof
{-@ appendGroup 
  :: x1:List a 
  -> x2:List a 
  -> x3:List a 
  -> x4:List a 
  -> x5:List a 
  -> {   (append (append x1 x2) (append (append x3 x4) x5))
      == (append x1 (append (append (append x2 x3) x4) x5))
     } @-}
appendGroup x1 x2 x3 x4 x5 
  =   listAssoc x1 x2 (append (append x3 x4) x5)
  &&& listAssoc x2 (append x3 x4) x5 
  &&& listAssoc x2 x3 x4 

{-@ automatic-instances appendUnGroup @-}

appendUnGroup :: List a -> List a -> List a -> List a -> List a -> Proof
{-@ appendUnGroup 
  :: x1:List a 
  -> x2:List a 
  -> x3:List a 
  -> x4:List a 
  -> x5:List a 
  -> {   (append x1 (append (append (append x2 x3) x4) x5))
      == (append (append (append (append x1 x2) x3) x4) x5)
     } @-}
appendUnGroup x1 x2 x3 x4 x5 
  =   listAssoc x2 x3 x4 
  &&& listAssoc x1 (append x2 (append x3 x4)) x5 
  &&& listAssoc x1 x2 (append x3 x4) 
  &&& listAssoc (append x1 x2) x3 x4


{-@ automatic-instances mapAppend @-}

mapAppend :: (a -> b) -> List a -> List a -> Proof
{-@ mapAppend 
     :: f:(a -> b) -> xs:List a -> ys:List a 
     -> {map f (append xs ys) == append (map f xs) (map f ys)}
  @-}
mapAppend f N ys 
  = trivial  
mapAppend f (C x xs) ys 
  = mapAppend f xs ys 
