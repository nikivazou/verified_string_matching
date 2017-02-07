#define IncludedcatIndices

#ifdef IncludedmakeIndicesNull
#else  
#include "../AutoProofs/makeIndicesNull.hs"   
#endif

#ifdef IncludedmergeIndices
#else  
#include "../AutoProofs/mergeIndices.hs"   
#endif

#ifdef IncludedconcatMakeIndices
#else  
#include "../AutoProofs/concatMakeIndices.hs"   
#endif

{-@ automatic-instances catIndices @-}

catIndices :: RString -> RString -> RString -> Int -> Int -> Proof 
{-@ catIndices 
     :: input:RString -> x:RString 
     -> target:{RString | 0 <= stringLen input - stringLen target + 1} 
     -> lo:{Nat | lo <= stringLen input - stringLen target } 
     -> hi:{Int | (stringLen input - stringLen target) <= hi}
     -> { makeIndices input target lo hi == makeIndices (input <+> x) target lo (stringLen input - stringLen target) }
  @-}
catIndices input x target lo hi 
  =   mergeIndices input target lo (stringLen input - stringLen target) hi
  &&& makeIndicesNull input target (stringLen input - stringLen target + 1) hi
  &&& listLeftId (makeIndices input target lo (stringLen input - stringLen target))
  &&& concatMakeIndices lo (stringLen input - stringLen target) target input x 
