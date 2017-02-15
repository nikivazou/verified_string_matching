#define IncludedListLemmata

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
  =   append (append x1 x2) (append (append x3 x4) x5)
  ==. append x1 (append x2 (append (append x3 x4) x5))
      ? listAssoc x1 x2 (append (append x3 x4) x5)
  ==. append x1 (append (append x2 (append x3 x4)) x5)
      ? listAssoc x2 (append x3 x4) x5 
  ==. append x1 (append (append (append x2 x3) x4) x5)
      ? listAssoc x2 x3 x4 
  *** QED 

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
  =   append x1 (append (append (append x2 x3) x4) x5)
  ==. append x1 (append (append x2 (append x3 x4)) x5)
      ? listAssoc x2 x3 x4 
  ==. append (append x1 (append x2 (append x3 x4))) x5
      ? listAssoc x1 (append x2 (append x3 x4)) x5 
  ==. append (append (append x1 x2) (append x3 x4)) x5
      ? listAssoc x1 x2 (append x3 x4) 
  ==. append (append (append (append x1 x2) x3) x4) x5
      ? listAssoc (append x1 x2) x3 x4
  *** QED


mapAppend :: (a -> b) -> List a -> List a -> Proof
{-@ mapAppend 
     :: f:(a -> b) -> xs:List a -> ys:List a 
     -> {map f (append xs ys) == append (map f xs) (map f ys)}
  @-}
mapAppend f N ys 
  =   map f (append N ys)
  ==. map f ys 
  ==. append N (map f ys)
  ==. append (map f N) (map f ys)
  *** QED 
mapAppend f (C x xs) ys 
  =   map f (append (C x xs) ys)
  ==. map f (x `C` (append xs ys))
  ==. f x `C` (map f (append xs ys))
  ==. f x `C` (append (map f xs) (map f ys))
      ? mapAppend f xs ys 
  ==. append (f x `C` map f xs) (map f ys)
  ==. append (map f (x `C` xs)) (map f ys)
  *** QED 
