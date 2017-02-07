#define IncludedshiftNewIndicesRight

#ifdef IncludedshiftIndicesRight
#else  
#include "../AutoProofs/shiftIndicesRight.hs"   
#endif

{-@ automatic-instances shiftNewIndicesRight @-}

{-@ shiftNewIndicesRight
  :: xi:RString 
  -> yi:RString 
  -> zi:RString 
  -> tg:{RString | stringLen tg <= stringLen yi } 
  -> { map (shiftStringRight tg xi (yi <+> zi)) (makeNewIndices yi zi tg) == makeNewIndices (xi <+> yi) zi tg }
  @-}
shiftNewIndicesRight :: RString -> RString -> RString -> RString -> Proof
shiftNewIndicesRight xi yi zi tg
  | stringLen tg < 2 
  =   trivial 
shiftNewIndicesRight xi yi zi tg
  =   makeNewIndices (xi <+> yi) zi tg  
  ==. makeIndices ((xi <+> yi) <+> zi) tg 
                   (maxInt (stringLen (xi <+> yi) - (stringLen tg - 1)) 0)
                   (stringLen (xi <+> yi) - 1 )
  ==. makeIndices (xi <+> (yi <+> zi)) tg 
                   (stringLen xi + stringLen yi - stringLen tg + 1)
                   (stringLen xi + stringLen yi - 1 )
      ?stringAssoc xi yi zi
  ==. map (shiftStringRight tg xi (yi <+> zi)) (makeIndices (yi <+> zi) tg (stringLen yi - stringLen tg + 1) (stringLen yi - 1))
      ?shiftIndicesRight (stringLen yi - stringLen tg + 1)
                         (stringLen yi - 1)
                         xi 
                         (yi <+> zi)
                         tg 
  ==. map (shiftStringRight tg xi (yi <+> zi)) 
               (makeIndices (yi <+> zi) tg 
                            (maxInt (stringLen yi - (stringLen tg -1)) 0)
                            (stringLen yi -1))
  ==. map (shiftStringRight tg xi (yi <+> zi)) 
          (makeNewIndices yi zi tg)
  *** QED
