#define IncludedmapLenFusion

{-@ automatic-instances mapLenFusion @-}

mapLenFusion :: RString -> RString -> RString -> RString -> List Int -> Proof
{-@ mapLenFusion :: tg:RString -> xi:RString -> yi:RString -> zi:RString 
            -> zis:List (GoodIndex zi tg) 
        -> {map (shiftStringRight tg xi (yi <+> zi)) (map (shiftStringRight tg yi zi) zis) == map (shiftStringRight tg (xi <+> yi) zi) zis} 
        / [llen zis ] @-}
mapLenFusion tg xi yi zi N  
  = trivial 
mapLenFusion tg xi yi zi (C i is)  
  =  mapLenFusion tg xi yi zi is
  &&& ( shiftStringRight tg xi (yi <+> zi) (shiftStringRight tg yi zi i)
    ==. shiftStringRight tg (xi <+> yi) zi i
    *** QED)


