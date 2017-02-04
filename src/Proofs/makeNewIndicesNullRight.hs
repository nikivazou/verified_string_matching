#define IncludedmakeNewIndicesNullRight

makeNewIndicesNullRight :: RString -> RString -> Proof 
{-@ makeNewIndicesNullRight 
  :: s1:RString 
  -> t:RString 
  -> {makeNewIndices stringEmp s1 t == N } @-} 
makeNewIndicesNullRight s t 
  | stringLen t < 2 
  = makeNewIndices stringEmp s t  ==. N *** QED 
makeNewIndicesNullRight s t 
  =   makeNewIndices stringEmp s t
  ==. makeIndices (stringEmp <+> s) t
                  (maxInt (1 + stringLen stringEmp - stringLen t) 0)
                  (stringLen stringEmp - 1)
  ==. makeIndices (stringEmp <+> s) t 0 (-1)
  ==. N  
  *** QED
