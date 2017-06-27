#define IncludedcatIndices

#ifdef IncludedmakeIndicesNull
#else  
#include "../Proofs/makeIndicesNull.hs"   
#endif

#ifdef IncludedmergeIndices
#else  
#include "../Proofs/mergeIndices.hs"   
#endif

#ifdef IncludedconcatMakeIndices
#else  
#include "../Proofs/concatMakeIndices.hs"   
#endif

catIndices :: RString -> RString -> RString -> Integer -> Integer -> Proof 
{-@ catIndices 
     :: input:RString -> x:RString 
     -> target:{RString | 0 <= stringLen input - stringLen target + 1} 
     -> lo:{INat | lo <= stringLen input - stringLen target } 
     -> hi:{Integer | (stringLen input - stringLen target) <= hi}
     -> { makeIndices input target lo hi == makeIndices (input <+> x) target lo (stringLen input - stringLen target) }
  @-}
catIndices input x target lo hi 
  =   makeIndices input target lo hi
  ==. append (makeIndices input target lo (stringLen input - stringLen target))
                  (makeIndices input target (stringLen input - stringLen target + 1) hi)
       ?mergeIndices input target lo (stringLen input - stringLen target) hi
  ==. append (makeIndices input target lo (stringLen input - stringLen target)) N
       ?makeIndicesNull input target (stringLen input - stringLen target + 1) hi
  ==. makeIndices input target lo (stringLen input - stringLen target)
       ?listLeftId (makeIndices input target lo (stringLen input - stringLen target))
  ==. makeIndices (input <+> x) target lo (stringLen input - stringLen target)
       ?concatMakeIndices lo (stringLen input - stringLen target) target input x 
  *** QED 
