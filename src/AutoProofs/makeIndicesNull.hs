#define IncludedmakeIndicesNull

{-@ automatic-instances makeIndicesNull @-}

makeIndicesNull :: RString -> RString -> Int -> Int -> Proof 
{-@ makeIndicesNull 
  :: s:RString 
  -> t:RString
  -> lo:Nat 
  -> hi:{Int | (stringLen t < 2 + stringLen s && 1 + stringLen s - stringLen t <= lo && lo <= hi)
             || (1 + stringLen s <= stringLen t)
             || (stringLen s < lo + stringLen t)
             || (stringLen s < stringLen t)}
  -> {makeIndices s t lo hi == N } / [hi - lo +1] @-} 
makeIndicesNull s1 t lo hi
  | hi < lo 
  = trivial  
makeIndicesNull s1 t lo hi
  | not (isGoodIndex s1 t lo)
  = makeIndicesNull s1 t (lo+1) hi
