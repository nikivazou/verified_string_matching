{-@ automatic-instances leftIdList @-}


{-@ leftIdList :: xs:L a -> {mappendList memptyList xs = xs} @-} 
leftIdList :: L a -> Proof 
leftIdList xs 
  =   mappendList memptyList xs 
  ==. mappendList N xs 
  ==. xs 
  *** QED 

{-@ rightIdList :: xs:L a -> {mappendList xs memptyList = xs} @-} 
rightIdList :: L a -> Proof 
rightIdList N        
  =   mappendList N memptyList
  ==. memptyList
  ==. N 
  *** QED 
rightIdList (C x xs) 
  =   mappendList (C x xs) memptyList
  ==. C x (mappendList xs memptyList)
  ==. C x xs  ? rightIdList xs 
  *** QED 

{-@ assocList :: xs:L a -> ys:L a -> zs:L a 
              -> {mappendList xs (mappendList ys zs) = mappendList (mappendList xs ys) zs} @-} 
assocList :: L a -> L a -> L a -> Proof 
assocList N ys zs          
  =   mappendList N (mappendList ys zs)
  ==. mappendList ys zs
  ==. mappendList (mappendList N ys) zs
  *** QED 
assocList (C x xs) ys zs 
  =   mappendList (C x xs) (mappendList ys zs)
  ==. C x (mappendList xs (mappendList ys zs))
  ==. C x (mappendList (mappendList xs ys) zs)
      ? assocList xs ys zs
  ==. mappendList (C x (mappendList xs ys)) zs 
  ==. mappendList (mappendList (C x xs) ys) zs
  *** QED 

{-@ takeDropPropList :: i:Nat -> xs:{L a | i <= length xs}  -> {xs == mappendList (takeList i xs) (dropList i xs)} / [length xs] @-}
takeDropPropList :: Nat -> L a -> Proof 
takeDropPropList i xs | i == 0 
  =   mappendList (takeList i xs) (dropList i xs)
  ==. mappendList N xs 
  ==. xs ? leftIdList xs 
  *** QED 
takeDropPropList i (C x xs)    
  =   mappendList (takeList i (C x xs)) (dropList i (C x xs)) 
  ==. mappendList (x `C` (takeList (i-1) xs)) (dropList (i-1) xs)
  ==. x `C` (mappendList (takeList (i-1) xs) (dropList (i-1) xs))
  ==. x `C` xs ? takeDropPropList (i-1) xs 
  *** QED 
