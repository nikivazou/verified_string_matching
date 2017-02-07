#define IncludedcastShift

{-@ automatic-instances castShift @-}

castShift :: RString -> RString -> RString -> RString -> List Int -> Proof
{-@ castShift :: tg:RString -> xi:RString -> yi:RString -> zi:RString 
             ->  yis:List (GoodIndex yi tg) 
        -> {map (castGoodIndexRight tg (xi <+> yi) zi) (map (shiftStringRight tg xi yi) yis) == map (shiftStringRight tg xi (yi <+> zi)) (map (castGoodIndexRight tg yi zi) yis)} @-}
castShift tg xi yi zi yis 
  =   map (castGoodIndexRight tg (xi <+> yi) zi) (map (shiftStringRight tg xi yi) yis)
  ==. map (shiftStringRight tg xi yi) yis  
        ? mapCastId tg (xi <+> yi) zi (map (shiftStringRight tg xi yi) yis)
  ==. map (shiftStringRight tg xi ((<+>) yi zi)) (map (castGoodIndexRight tg yi zi) yis)
        ? (mapShiftIndex tg xi yi zi yis &&& mapCastId tg yi zi yis)
  *** QED 

{-@ automatic-instances mapShiftIndex @-}

{-@ mapShiftIndex :: tg:RString -> xi:RString -> yi:RString -> zi:RString -> xs:List (GoodIndex yi tg)
  -> {map (shiftStringRight tg xi yi) xs == map (shiftStringRight tg xi (yi <+> zi)) xs} / [llen xs] @-}
mapShiftIndex :: RString -> RString -> RString -> RString -> List Int -> Proof
mapShiftIndex tg xi yi zi N 
  = trivial 
mapShiftIndex tg xi yi zi zs@(C i0 is0)
  = let is = cast (mapCastId tg yi zi is0) $ map (castGoodIndexRight tg yi zi) is0 in 
    mapShiftIndex tg xi yi zi is
