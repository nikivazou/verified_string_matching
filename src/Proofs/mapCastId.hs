mapCastId :: RString -> RString -> RString -> List Int -> Proof 
{-@ mapCastId :: tg:RString -> x:RString -> y:RString -> is:List (GoodIndex x tg) -> 
      {map (castGoodIndexRight tg x y) is == is} @-}
mapCastId tg x y N 
  = map (castGoodIndexRight tg x y) N ==. N *** QED 
mapCastId tg x y (C i is) 
  =   map (castGoodIndexRight tg x y) (C i is) 
  ==. castGoodIndexRight tg x y i `C` map (castGoodIndexRight tg x y) is 
  ==. i `C` is ? mapCastId tg x y is  
  *** QED 
