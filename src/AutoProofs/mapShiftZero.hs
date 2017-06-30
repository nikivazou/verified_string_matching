#define IncludedmapShiftZero

{-@ automatic-instances mapShiftZero @-}

mapShiftZero :: RString -> RString -> List Integer -> Proof
{-@ mapShiftZero :: target:RString -> i:RString -> is:List (GoodIndex i target) 
  -> {map (shiftStringRight target stringEmp i) is == is } 
  / [llen is] @-}
mapShiftZero target i N
  = trivial
mapShiftZero target i (C x xs)
  = mapShiftZero target i xs 
