#define IncludedmergeIndices

{-@ automatic-instances mergeIndices @-}

mergeIndices :: RString -> RString -> Integer -> Integer -> Integer -> Proof
{-@ mergeIndices 
  :: input:RString -> target:RString -> lo:INat -> mid:{Integer | lo <= mid} -> hi:{Integer | mid <= hi} 
  -> {makeIndices input target lo hi == append (makeIndices input target lo mid) (makeIndices input target (mid+1) hi)} 
  / [mid] @-}
mergeIndices input target lo mid hi 
  | lo == mid, isGoodIndex input target lo 
  = trivial 
  | lo == mid, not (isGoodIndex input target lo)
  = trivial 
  | lo < mid, not (isGoodIndex input target mid)
  =   mergeIndices input target lo (mid-1) hi 
  &&& makeNewIndicesBadLast input target lo mid
  | lo < mid, isGoodIndex input target mid
  =   mergeIndices input target lo (mid-1) hi 
  &&& listAssoc (makeIndices input target lo (mid-1)) (C mid N) (makeIndices input target (mid+1) hi)
  &&& makeNewIndicesGoodLast input target lo mid

{-@ automatic-instances makeNewIndicesGoodLast @-}
{-@ automatic-instances makeNewIndicesBadLast  @-}

makeNewIndicesGoodLast, makeNewIndicesBadLast 
  :: RString -> RString -> Integer -> Integer -> Proof 
{-@ makeNewIndicesGoodLast 
  :: input:RString -> target:RString -> lo:INat -> hi:{Integer | lo <= hi && (isGoodIndex input target hi)}
  -> {makeIndices input target lo hi == append (makeIndices input target lo (hi-1)) (C hi N)}
  / [hi - lo] @-}
makeNewIndicesGoodLast input target lo hi 
  | lo == hi, (isGoodIndex input target lo)
  = trivial 
  | not (isGoodIndex input target lo), isGoodIndex input target hi 
  =   makeNewIndicesGoodLast input target (lo+1) hi
  | isGoodIndex input target lo, isGoodIndex input target hi
  = makeNewIndicesGoodLast input target (lo+1) hi  
  

{-@ makeNewIndicesBadLast 
  :: input:RString -> target:RString -> lo:INat -> hi:{Integer | lo <= hi && (not (isGoodIndex input target hi))}
  -> {makeIndices input target lo hi == makeIndices input target lo (hi-1)}
  / [hi - lo + 1]
@-}
-- NV sweet proof 
makeNewIndicesBadLast input target lo hi 
  | lo == hi, not (isGoodIndex input target lo)
  = trivial 
  | not (isGoodIndex input target lo), not (isGoodIndex input target hi) 
  = makeNewIndicesBadLast input target (lo+1) hi   
  | isGoodIndex input target lo , not (isGoodIndex input target hi) 
  = makeNewIndicesBadLast input target (lo+1) hi   

