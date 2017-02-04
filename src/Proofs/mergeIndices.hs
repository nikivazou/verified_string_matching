#define IncludedmergeIndices

mergeIndices :: RString -> RString -> Int -> Int -> Int -> Proof
{-@ mergeIndices 
  :: input:RString -> target:RString -> lo:Nat -> mid:{Int | lo <= mid} -> hi:{Int | mid <= hi} 
  -> {makeIndices input target lo hi == append (makeIndices input target lo mid) (makeIndices input target (mid+1) hi)} 
  / [mid] @-}
mergeIndices input target lo mid hi 
  | lo == mid, isGoodIndex input target lo 
  =   append (makeIndices input target lo mid) (makeIndices input target (mid+1) hi)
  ==. append (makeIndices input target lo lo)  (makeIndices input target (mid+1) hi)
  ==. append (lo `C` (makeIndices input target (lo+1) lo))  (makeIndices input target (mid+1) hi)
  ==. append (lo `C` N)  (makeIndices input target (mid+1) hi)
  ==. lo  `C` (append N  (makeIndices input target (lo+1) hi))
  ==. lo  `C` (makeIndices input target (lo+1) hi)
  ==. makeIndices input target lo hi
  *** QED 
  | lo == mid, not (isGoodIndex input target lo)
  =   append (makeIndices input target lo mid) (makeIndices input target (mid+1) hi)
  ==. append (makeIndices input target lo lo)  (makeIndices input target (mid+1) hi)
  ==. append (lo `C` makeIndices input target (lo+1) lo)  (makeIndices input target (mid+1) hi)
  ==. append (lo `C` N)  (makeIndices input target (mid+1) hi)
  ==. (append N  (makeIndices input target (lo+1) hi))
  ==. makeIndices input target lo hi
  *** QED 
  | lo < mid, not (isGoodIndex input target mid)
  =   makeIndices input target lo hi
  ==. append (makeIndices input target lo (mid-1)) 
                  (makeIndices input target mid hi)
      ?mergeIndices input target lo (mid-1) hi 
  ==. append (makeIndices input target lo (mid-1)) 
                  (makeIndices input target (mid+1) hi)
  ==. append (makeIndices input target lo mid) 
                  (makeIndices input target (mid+1) hi)
      ?makeNewIndicesBadLast input target lo mid
  *** QED 
  | lo < mid, isGoodIndex input target mid
  =   makeIndices input target lo hi
  ==. append (makeIndices input target lo (mid-1)) 
                  (makeIndices input target mid hi)
      ?mergeIndices input target lo (mid-1) hi 
  ==. append (makeIndices input target lo (mid-1)) 
                  (mid `C` makeIndices input target (mid+1) hi)
  ==. append (makeIndices input target lo (mid-1)) 
                  (mid `C` (append N (makeIndices input target (mid+1) hi)))
  ==. append (makeIndices input target lo (mid-1)) 
                  (append (C mid N) (makeIndices input target (mid+1) hi))
  ==. append (append (makeIndices input target lo (mid-1)) (C mid N)) 
                  (makeIndices input target (mid+1) hi)
      ? listAssoc (makeIndices input target lo (mid-1)) (C mid N) (makeIndices input target (mid+1) hi)
  ==. append (makeIndices input target lo mid) 
                  (makeIndices input target (mid+1) hi)
      ?makeNewIndicesGoodLast input target lo mid
  *** QED 


makeNewIndicesGoodLast, makeNewIndicesBadLast 
  :: RString -> RString -> Int -> Int -> Proof 
{-@ makeNewIndicesGoodLast 
  :: input:RString -> target:RString -> lo:Nat -> hi:{Int | lo <= hi && (isGoodIndex input target hi)}
  -> {makeIndices input target lo hi == append (makeIndices input target lo (hi-1)) (C hi N)}
  / [hi - lo] @-}
makeNewIndicesGoodLast input target lo hi 
  | lo == hi, (isGoodIndex input target lo)
  =   makeIndices input target lo hi 
  ==. hi `C` makeIndices input target (lo+1) hi  
  ==. hi `C` N 
  ==. append (N) (C hi N)
  ==. append (makeIndices input target lo (hi-1)) (C hi N)
  *** QED 
  | not (isGoodIndex input target lo), isGoodIndex input target hi 
  =   makeIndices input target lo hi 
  ==. makeIndices input target (lo+1) hi
  ==. append (makeIndices input target (lo+1) (hi-1)) (C hi N)
       ? makeNewIndicesGoodLast input target (lo+1) hi  
  ==. append (makeIndices input target lo (hi-1)) (C hi N)
  *** QED 
  | isGoodIndex input target lo, isGoodIndex input target hi
  =   makeIndices input target lo hi 
  ==. lo `C` makeIndices input target (lo+1) hi
  ==. lo `C` (append (makeIndices input target (lo+1) (hi-1)) (C hi N))
       ? makeNewIndicesGoodLast input target (lo+1) hi  
  ==. (append (lo `C` makeIndices input target (lo+1) (hi-1)) (C hi N))
  ==. append (makeIndices input target lo (hi-1)) (C hi N)
  *** QED 

{-@ makeNewIndicesBadLast 
  :: input:RString -> target:RString -> lo:Nat -> hi:{Int | lo <= hi && (not (isGoodIndex input target hi))}
  -> {makeIndices input target lo hi == makeIndices input target lo (hi-1)}
  / [hi - lo + 1]
@-}
-- NV sweet proof 
makeNewIndicesBadLast input target lo hi 
  | lo == hi, not (isGoodIndex input target lo)
  =   makeIndices input target lo (hi-1) 
  ==. N 
  ==. makeIndices input target (lo+1) hi
  ==. makeIndices input target lo hi
  *** QED 
  | not (isGoodIndex input target lo), not (isGoodIndex input target hi) 
  =   makeIndices input target lo hi 
  ==. makeIndices input target (lo+1) hi
  ==. makeIndices input target (lo+1) (hi-1)
       ? makeNewIndicesBadLast input target (lo+1) hi   
  ==. makeIndices input target lo (hi-1)
  *** QED 
  | isGoodIndex input target lo , not (isGoodIndex input target hi) 
  =   makeIndices input target lo hi 
  ==. lo `C` makeIndices input target (lo+1) hi
  ==. lo `C` makeIndices input target (lo+1) (hi-1)
       ? makeNewIndicesBadLast input target (lo+1) hi   
  ==. makeIndices input target lo (hi-1)
  *** QED 