#define IncludedmapCastId

{-@ automatic-instances mapCastId @-}

mapCastId :: RString -> RString -> RString -> List Integer -> Proof 
{-@ mapCastId :: tg:RString -> x:RString -> y:RString -> is:List (GoodIndex x tg) -> 
      {map (castGoodIndexRight tg x y) is == is} @-}
mapCastId tg x y N 
  = trivial 
mapCastId tg x y (C i is) 
  = mapCastId tg x y is  
