
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

castConcat :: RString -> RString -> RString -> RString -> List Int -> Proof
{-@ castConcat :: tg:RString -> xi:RString -> yi:RString -> zi:RString 
             ->  xis:List (GoodIndex xi tg) 
        -> { map (castGoodIndexRight tg xi (yi <+> zi)) xis == map (castGoodIndexRight tg (xi <+> yi) zi) (map (castGoodIndexRight tg xi yi) xis)} @-}
castConcat tg xi yi zi xis
  =    map (castGoodIndexRight tg xi (yi <+> zi)) xis 
  ==.  xis 
       ? mapCastId tg xi (yi <+> zi) xis 
  ==. (map (castGoodIndexRight tg xi yi) xis)
       ? mapCastId tg xi yi xis  
  ==. map (castGoodIndexRight tg (xi <+> yi) zi) (map (castGoodIndexRight tg xi yi) xis)
       ? mapCastId tg (xi <+> yi) zi (map (castGoodIndexRight tg xi yi) xis) 
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


mapCastId :: RString -> RString -> RString -> List Int -> Proof 
{-@ mapCastId :: tg:RString -> x:RString -> y:RString -> is:List (GoodIndex x tg) -> 
      {map (castGoodIndexRight tg x y) is == is} @-}
mapCastId tg x y N 
  = map (castGoodIndexRight tg x y) N ==. N *** QED 
mapCastId tg x y (C i is) 
  =   map (castGoodIndexRight tg x y) (C i is) 
  ==. castGoodIndexRight tg x y i `C` map (castGoodIndexRight tg x y) is 
  ==. i `C` is 
       ? mapCastId tg x y is  
  *** QED 
