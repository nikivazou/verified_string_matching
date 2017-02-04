makeNewIndicesNullLeft :: RString -> RString -> Proof 
{-@ makeNewIndicesNullLeft 
  :: s:RString 
  -> t:RString 
  -> {makeNewIndices s stringEmp t == N } @-} 
makeNewIndicesNullLeft s t 
  | stringLen t < 2 
  = makeNewIndices s stringEmp t ==. N *** QED 
makeNewIndicesNullLeft  s t 
  | 1 + stringLen s <= stringLen t
  =   makeNewIndices s stringEmp t
  ==. makeIndices ((<+>) s stringEmp) t
                   (maxInt (1 + stringLen s - stringLen t)  0)
                   (stringLen s - 1)
  ==. makeIndices s t
                   0
                   (stringLen s - 1) 
                   ? concatStringNeutralLeft s
  ==. makeIndices s t
                   0
                   (stringLen s - 1)
  ==. N ? makeNewIndicesNullSmallInput s t 0 (stringLen s - 1)
  *** QED 
makeNewIndicesNullLeft s t 
  =   makeNewIndices s stringEmp t
  ==. makeIndices ((<+>) s stringEmp) t
                   (maxInt (1 + stringLen s - stringLen t)  0)
                   (stringLen s - 1)
  ==. makeIndices ((<+>) s stringEmp) t
                   (1 + stringLen s - stringLen t)
                   (stringLen s - 1)
  ==. makeIndices s t
                   (1 + stringLen s - stringLen t)
                   (stringLen s - 1) ? concatStringNeutralLeft s 
  ==. N ? makeNewIndicesNullSmallIndex s t (1 + stringLen s - stringLen t) (stringLen s - 1)
  *** QED 

makeNewIndicesNullSmallInput :: RString -> RString -> Int -> Int -> Proof 
{-@ makeNewIndicesNullSmallInput 
  :: s:RString 
  -> t:{RString | 1 + stringLen s <= stringLen t } 
  -> lo:Nat 
  -> hi:Int
  -> {makeIndices s t lo hi == N } / [hi - lo + 1] @-} 
makeNewIndicesNullSmallInput s1 t lo hi
  | hi < lo 
  = makeIndices s1 t lo hi ==. N *** QED 
  | not (isGoodIndex s1 t lo)
  =   makeIndices s1 t lo hi
  ==. makeIndices s1 t (lo + 1) hi 
  ==. N ? makeNewIndicesNullSmallInput s1 t (lo+1) hi
  *** QED 


makeNewIndicesNullSmallIndex :: RString -> RString -> Int -> Int -> Proof 
{-@ makeNewIndicesNullSmallIndex 
  :: s:RString 
  -> t:{RString | stringLen t < 2 + stringLen s } 
  -> lo:{Nat | 1 + stringLen s - stringLen t <= lo  } 
  -> hi:{Int | lo <= hi}
  -> {makeIndices s t lo hi == N } / [hi - lo +1] @-} 
makeNewIndicesNullSmallIndex s1 t lo hi
  | lo == hi, not (isGoodIndex s1 t lo)
  =   makeIndices s1 t lo hi 
  ==. makeIndices s1 t (lo+1) lo 
  ==. N *** QED  
  | not (isGoodIndex s1 t lo)
  =   makeIndices s1 t lo hi
  ==. makeIndices s1 t (lo + 1) hi 
  ==. N ? makeNewIndicesNullSmallIndex s1 t (lo+1) hi
  *** QED 