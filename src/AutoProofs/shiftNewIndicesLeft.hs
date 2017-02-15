#define IncludedshiftNewIndicesLeft
#ifdef IncludedmapCastId
#else  
#include "../AutoProofs/mapCastId.hs"   
#endif
#ifdef IncludedconcatMakeIndices
#else  
#include "../AutoProofs/concatMakeIndices.hs"   
#endif
{-@ shiftNewIndicesLeft
  :: xi:RString 
  -> yi:RString 
  -> zi:RString 
  -> tg:{RString | stringLen tg <= stringLen yi } 
  -> {  makeNewIndices xi (yi <+> zi) tg == map (castGoodIndexRight tg (xi <+> yi) zi) (makeNewIndices xi yi tg)}
  @-}

shiftNewIndicesLeft :: RString -> RString -> RString -> RString -> Proof
shiftNewIndicesLeft xi yi zi tg
  | stringLen tg < 2 
  =   makeNewIndices xi (yi <+> zi) tg 
  ==. N
  ==. makeNewIndices xi yi tg 
  ==. map (castGoodIndexRight tg (xi <+> yi) zi) (makeNewIndices xi yi tg)
      ?mapCastId tg (xi <+> yi) zi (makeNewIndices xi yi tg)
  *** QED 
  | otherwise
  =   makeNewIndices xi (yi <+> zi) tg 
  ==. makeIndices (xi <+> (yi <+> zi)) tg 
                   (maxInt (stringLen xi - (stringLen tg-1)) 0)
                   (stringLen xi - 1)
  ==. makeIndices ((xi <+> yi) <+> zi) tg 
                   (maxInt (stringLen xi - (stringLen tg-1)) 0)
                   (stringLen xi - 1)
     ?stringAssoc xi yi zi 
  ==. makeIndices (xi <+> yi) tg 
                  (maxInt (stringLen xi - (stringLen tg-1)) 0)
                  (stringLen xi - 1)                
      ?concatMakeIndices (maxInt (stringLen xi - (stringLen tg-1)) 0) (stringLen xi - 1) tg (xi <+> yi) zi 
  ==. makeNewIndices xi yi tg 
  ==. map (castGoodIndexRight tg (xi <+> yi) zi) (makeNewIndices xi yi tg)
      ?mapCastId tg (xi <+> yi) zi (makeNewIndices xi yi tg)
  *** QED 
