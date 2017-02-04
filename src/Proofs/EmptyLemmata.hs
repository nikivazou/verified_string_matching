-------------------------------------------------------------------------------
----------  Lemmata on Empty Indices ------------------------------------------
-------------------------------------------------------------------------------

emptyIndices :: forall (target :: Symbol). (KnownSymbol target) => SM target -> List Int  -> Proof
{-@ emptyIndices :: mi:SM target
                 -> is:{List (GoodIndex (inputSM mi) target) | is == indicesSM mi && stringLen (inputSM mi) < stringLen target}
                 -> { is == N } @-}
emptyIndices (SM _ _) N 
  = trivial 
emptyIndices (SM _ _) (C _ _)
  = trivial 

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
  ==. makeIndices ((<+>) stringEmp s) t
                   (maxInt (1 + stringLen stringEmp - stringLen t) 0)
                   (stringLen stringEmp - 1)
  ==. makeIndices s t
                   (maxInt (1 - stringLen t) 0)
                   (-1)
      ? concatStringNeutralRight s 
  ==. makeIndices s t 0 (-1)
  ==. N  
  *** QED


mapShiftZero :: RString -> RString -> List Int -> Proof
{-@ mapShiftZero :: target:RString -> i:RString -> is:List (GoodIndex i target) 
  -> {map (shiftStringRight target stringEmp i) is == is } 
  / [llen is] @-}
mapShiftZero target i N
  =   map (shiftStringRight target stringEmp i) N ==. N *** QED  
mapShiftZero target i (C x xs)
  =   map (shiftStringRight target stringEmp i) (C x xs) 
  ==. shiftStringRight target stringEmp i x `C` map (shiftStringRight target stringEmp i) xs
  ==. shift (stringLen stringEmp) x `C` map (shiftStringRight target stringEmp i) xs
  ==. shift 0 x `C` map (shiftStringRight target stringEmp i) xs
  ==. x `C` map (shiftStringRight target stringEmp i) xs
  ==. x `C` xs ? mapShiftZero target i xs 
  *** QED 


{-@ toSMEmpty :: SM target -> x:{RString | stringLen x == 0} -> {toSM x == mempty} @-}
toSMEmpty :: forall (target :: Symbol). (KnownSymbol target) =>  SM target ->  RString -> Proof
toSMEmpty _ x
  =   toSM x 
  ==. SM x (makeSMIndices x tg)
  ==. SM x (makeIndices x tg 0 (stringLen x -1))
       ? stringEmpProp x 
  ==. SM stringEmp N 
  ==. (mempty :: SM target)
  *** QED 
  where 
    tg  = fromString (symbolVal (Proxy :: Proxy target))
