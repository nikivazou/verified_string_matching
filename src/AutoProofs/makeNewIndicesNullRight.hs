#define IncludedmakeNewIndicesNullRight

{-@ automatic-instances makeNewIndicesNullRight @-}

makeNewIndicesNullRight :: RString -> RString -> Proof 
{-@ makeNewIndicesNullRight 
  :: s1:RString 
  -> t:RString 
  -> {makeNewIndices stringEmp s1 t == N } @-} 
makeNewIndicesNullRight s t 
  | stringLen t < 2 
  = trivial  
makeNewIndicesNullRight s t 
  = trivial 
