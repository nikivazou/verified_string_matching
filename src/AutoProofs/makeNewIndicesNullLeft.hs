#define IncludedmakeNewIndicesNullLeft
#ifdef IncludedmakeIndicesNull
#else  
#include "../AutoProofs/makeIndicesNull.hs"   
#endif

{-@ automatic-instances makeNewIndicesNullLeft @-}

makeNewIndicesNullLeft :: RString -> RString -> Proof 
{-@ makeNewIndicesNullLeft 
  :: s:RString 
  -> t:RString 
  -> {makeNewIndices s stringEmp t == N } @-} 
makeNewIndicesNullLeft s t 
  | stringLen t < 2 
  = trivial  
makeNewIndicesNullLeft s t 
  =   concatStringNeutralLeft s
  &&& makeIndicesNull s t (maxInt (1 + stringLen s - stringLen t)  0) (stringLen s - 1)
