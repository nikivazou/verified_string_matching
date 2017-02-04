
-------------------------------------------------------------------------------
----------  Lemmata on Casts --------------------------------------------------
-------------------------------------------------------------------------------

{-@ castAppend :: target:RString -> input:RString -> x:RString 
     -> is1:List (GoodIndex input target) 
     -> is2:List (GoodIndex input target) -> 
   {map (castGoodIndexRight target input x) (append is1 is2) == append (map (castGoodIndexRight target input x) is1) (map (castGoodIndexRight target input x) is2)}
    @-}
castAppend :: RString -> RString -> RString -> List Int -> List Int -> Proof 
castAppend target input x is1 is2 
  =   mapAppend (castGoodIndexRight target input x) is1 is2
  *** QED 

castEq3 :: RString -> RString -> RString -> RString -> List Int -> Proof
{-@ castEq3 :: tg:RString -> xi:RString -> yi:RString -> zi:RString 
             ->  yis:List (GoodIndex yi tg) 
        -> {map (castGoodIndexRight tg (xi <+> yi) zi) (map (shiftStringRight tg xi yi) yis) == map (shiftStringRight tg xi (yi <+> zi)) (map (castGoodIndexRight tg yi zi) yis)} @-}
castEq3 tg xi yi zi yis 
  =   map (castGoodIndexRight tg (xi <+> yi) zi) (map (shiftStringRight tg xi yi) yis)
  ==. map (shiftStringRight tg xi yi) yis  
        ? mapCastId tg (xi <+> yi) zi (map (shiftStringRight tg xi yi) yis)
  ==. map (shiftStringRight tg xi ((<+>) yi zi)) (map (castGoodIndexRight tg yi zi) yis)
        ? (mapShiftIndex tg xi yi zi yis &&& mapCastId tg yi zi yis)
  *** QED 

{-@ mapShiftIndex :: tg:RString -> xi:RString -> yi:RString -> zi:RString -> xs:List (GoodIndex yi tg)
  -> {map (shiftStringRight tg xi yi) xs == map (shiftStringRight tg xi (yi <+> zi)) xs} / [llen xs] @-}
mapShiftIndex :: RString -> RString -> RString -> RString -> List Int -> Proof
mapShiftIndex tg xi yi zi N 
  = map (shiftStringRight tg xi yi) N ==. N ==. map (shiftStringRight tg xi (yi <+> zi)) N *** QED 
  *** QED 
mapShiftIndex tg xi yi zi zs@(C i0 is0)
  =   let is = cast (mapCastId tg yi zi is0) $ map (castGoodIndexRight tg yi zi) is0 
          i  = castGoodIndexRight     tg yi zi i0  in 
      map (shiftStringRight tg xi yi) (C i is) 
  ==. C (shiftStringRight tg xi yi i) (map (shiftStringRight tg xi yi) is)
  ==. C (shift (stringLen xi) i) (map (shiftStringRight tg xi yi) is)
  ==. C (shiftStringRight tg xi (yi <+> zi) i) (map (shiftStringRight tg xi yi) is)
  ==. C (shiftStringRight tg xi (yi <+> zi) i) (map (shiftStringRight tg xi (yi <+> zi)) is)
       ? mapShiftIndex tg xi yi zi is
  ==. map (shiftStringRight tg xi (yi <+> zi)) (C i is)
  *** QED 
