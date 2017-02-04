#define IncludedmakeIndicesNull

makeIndicesNull :: RString -> RString -> Int -> Int -> Proof 
{-@ makeIndicesNull 
  :: s:RString 
  -> t:RString
  -> lo:Nat 
  -> hi:{Int | (stringLen t < 2 + stringLen s && 1 + stringLen s - stringLen t <= lo && lo <= hi)
             || (1 + stringLen s <= stringLen t)}
  -> {makeIndices s t lo hi == N } / [hi - lo +1] @-} 
makeIndicesNull s1 t lo hi
  | hi < lo 
  = makeIndices s1 t lo hi ==. N *** QED 
  | lo == hi, not (isGoodIndex s1 t lo)
  =   makeIndices s1 t lo hi 
  ==. makeIndices s1 t (lo+1) lo 
  ==. N *** QED  
  | not (isGoodIndex s1 t lo)
  =   makeIndices s1 t lo hi
  ==. makeIndices s1 t (lo + 1) hi 
  ==. N ? makeIndicesNull s1 t (lo+1) hi
  *** QED 