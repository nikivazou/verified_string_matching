#define IncludedmakeNewIndicesNullLeft
#ifdef IncludedmakeIndicesNull
#else  
#include "../Proofs/makeIndicesNull.hs"   
#endif

makeNewIndicesNullLeft :: RString -> RString -> Proof 
{-@ makeNewIndicesNullLeft 
  :: s:RString 
  -> t:RString 
  -> {makeNewIndices s stringEmp t == N } @-} 
makeNewIndicesNullLeft s t 
  | stringLen t < 2 
  = makeNewIndices s stringEmp t ==. N *** QED 
makeNewIndicesNullLeft s t 
  =   makeNewIndices s stringEmp t
  ==. makeIndices (s <+> stringEmp) t
                  (maxInt (1 + stringLen s - stringLen t)  0)
                  (stringLen s - 1)
  ==. makeIndices s t
                  (maxInt (1 + stringLen s - stringLen t)  0)
                  (stringLen s - 1)
      ? concatStringNeutralLeft s
  ==. N ? makeIndicesNull s t (maxInt (1 + stringLen s - stringLen t)  0) (stringLen s - 1)
  *** QED 