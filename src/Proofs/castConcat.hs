#define IncludedcastConcat

castConcat :: RString -> RString -> RString -> RString -> List Integer -> Proof
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
