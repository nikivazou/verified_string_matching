
{-@ equivalencePropDef :: stg:Strategy (L m) -> f:(n -> m) -> p:Morphism n m f -> i:Nat -> j:Nat -> x:n 
  -> { f x == parallelizeWithStrategyDef stg f p i j x } @-}
equivalencePropDef :: (ChunkableMonoid n, ChunkableMonoid m, Eq m) => Strategy (L m) -> (n -> m) -> Morphism n m -> Nat -> Nat -> n -> Proof 
equivalencePropDef stg f p i j x
  | i == 0 
  =   parallelizeWithStrategyDef stg f p i j x 
  ==. f x 
  *** QED  
equivalencePropDef stg f p i j x | 0 < i 
  =   parallelizeWithStrategyDef stg f p i j x
  ==. pmconcatWithStrategy stg j (pmapWithStrategy stg f (chunk i x))
  ==. mconcat (pmapWithStrategy stg f (chunk i x))
      ? pmconcatEquivalence stg j (pmapWithStrategy stg f (chunk i x))
  ==. mconcat (withStrategy stg (map f (chunk i x)))
  ==. mconcat (map f (chunk i x))
      ? morphismDistribution f p i x 
  ==. f x 
  *** QED  

{-@ morphismDistribution :: f:(n -> m) -> p:Morphism n m f -> i:Pos -> x:n 
  -> { f x  == mconcat (map f (chunk i x)) } / [length x] @-}
morphismDistribution :: (ChunkableMonoid n, ChunkableMonoid m) => (n -> m) -> Morphism n m -> Nat -> n -> Proof 
morphismDistribution f thm i x 
  | length x <= i 
  =   mconcat (map f (chunk i x))
  ==. mconcat (map f (C x N))
  ==. mconcat (f x `C` map f N)
  ==. mconcat (f x `C` N)
  ==. f x `mappend` mconcat N 
  ==. f x `mappend` mempty 
  ==. f x ? rightId (f x) 
  *** QED 
morphismDistribution f thm i x 
  =   mconcat (map f (chunk i x))
  ==. mconcat (map f (C (take i x) (chunk i (drop i x))))
  ==. mconcat (C (f (take i x)) (map f (chunk i (drop i x))))
  ==. mappend (f (take i x)) (mconcat (map f (chunk i (drop i x))))
  ==. mappend (f (take i x)) (f (drop i x))
      ? morphismDistribution f thm i (drop i x)
  ==. f (mappend (take i x) (drop i x))
      ? thm (take i x) (drop i x)
  ==. f x 
      ? takeDropProp i x 
  *** QED 


{-@ pmconcatEquivalence :: stg:Strategy (L n) -> j:Nat -> x:L n -> { pmconcatWithStrategy stg j x = mconcat x } / [length x] @-}
pmconcatEquivalence :: (Monoid n, Eq n) => Strategy (L n) -> Nat -> L n -> Proof 
pmconcatEquivalence stg j x 
  | j <= 1 || length x <= j 
  =   pmconcatWithStrategy stg j x
  ==. mconcat x 
  *** QED 
pmconcatEquivalence stg j x 
  =   pmconcatWithStrategy stg j x
  ==. pmconcatWithStrategy stg j (pmapWithStrategy stg mconcat (chunk j x))
  ==. pmconcatWithStrategy stg j (withStrategy stg (map mconcat (chunk j x)))
  ==. pmconcatWithStrategy stg j (map mconcat (chunk j x))
  ==. mconcat (map mconcat (chunk j x))
       ? pmconcatEquivalence stg j (map mconcat (chunk j x))
  ==. mconcat x 
       ? mconcatChunk j x 
  *** QED 



mconcatSplit :: (Monoid a, Eq a) => Pos -> L a -> Proof 
{-@ mconcatSplit :: i:Pos -> xs:{L a  | i <= length xs} 
     -> { mconcat xs ==  mappend (mconcat (takeList i xs)) (mconcat (dropList i xs))}
     / [i]
  @-} 

mconcatSplit i (C x xs)
  | i == 1 
  =   mappend (mconcat (takeList i (C x xs))) (mconcat (dropList i (C x xs))) 
  ==. mappend (mconcat (C x (takeList 0 xs))) (mconcat (dropList 0 xs))
  ==. mappend (mconcat (C x N))               (mconcat xs)
  ==. mappend (mappend x (mconcat N))         (mconcat xs)
  ==. mappend (mappend x mempty)              (mconcat xs)
  ==. mappend x (mconcat xs)
       ? rightId x 
  ==. mconcat (C x xs)
  *** QED 

mconcatSplit i (C x xs)
  =    mappend (mconcat (takeList i (C x xs)))           (mconcat (dropList i (C x xs))) 
  ==.  mappend (mconcat (C x (takeList (i-1) xs)))       (mconcat (dropList (i-1) xs))
  ==.  mappend (mappend x (mconcat (takeList (i-1) xs))) (mconcat (dropList (i-1) xs))
  ==.  x `mappend` (mappend (mconcat (takeList (i-1) xs)) (mconcat (dropList (i-1) xs)))
       ? assoc x (mconcat (takeList (i-1) xs)) (mconcat (dropList (i-1) xs))
  ==. x `mappend` mconcat xs
       ? mconcatSplit (i-1) xs
  ==. mconcat (C x xs)
  *** QED 
mconcatSplit i n
  =  mappend (mconcat (take i n))  (mconcat (drop i n))
  ==. mconcat n `mappend` mconcat n
  ==. mempty `mappend` mconcat n
  ==. mconcat n ? leftId (mconcat n)
  ==. mconcat n 
  *** QED 

mconcatChunk ::  (Monoid a, Eq a) => Pos -> L a  -> Proof 
{-@ mconcatChunk :: i:Pos -> xs:L a -> { mconcat xs == mconcat (map mconcat (chunk i xs))}
  /  [length xs] @-}
mconcatChunk i xs  
  | length xs <= i 
  =   mconcat (map mconcat (chunk i xs))
  ==. mconcat (map mconcat (C xs N))
  ==. mconcat (mconcat xs `C` map mconcat N)
  ==. mconcat (mconcat xs `C` N)
  ==. mconcat xs `mappend` mconcat N
  ==. mconcat xs `mappend` mempty
  ==. mconcat xs 
       ? rightId (mconcat xs)
  *** QED  
   | otherwise
   =   mconcat (map mconcat (chunk i xs))
   ==. mconcat (map mconcat (take i xs `C` chunk i (drop i xs)))
        ? takeListAssumed i xs &&& dropListAssumed i xs 
   ==. mconcat (map mconcat (takeList i xs `C` chunk i (dropList i xs)))
   ==. mconcat (mconcat (takeList i xs) `C` map mconcat (chunk i (dropList i xs)))
   ==. mconcat (takeList i xs) `mappend` (mconcat (map mconcat (chunk i (dropList i xs))))
   ==. mconcat (takeList i xs) `mappend` (mconcat (dropList i xs))
        ? mconcatChunk i (dropList i xs)
   ==. mconcat xs 
        ? mconcatSplit i xs 
   *** QED 
