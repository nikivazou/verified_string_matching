#define IncludedmapLenFusion

mapLenFusion :: RString -> RString -> RString -> RString -> List Integer -> Proof
{-@ mapLenFusion :: tg:RString -> xi:RString -> yi:RString -> zi:RString 
            -> zis:List (GoodIndex zi tg) 
        -> {map (shiftStringRight tg xi (yi <+> zi)) (map (shiftStringRight tg yi zi) zis) == map (shiftStringRight tg (xi <+> yi) zi) zis} 
        / [llen zis ] @-}
mapLenFusion tg xi yi zi N  
  =   map (shiftStringRight tg xi ((<+>) yi zi)) (map (shiftStringRight tg yi zi) N)
  ==. map (shiftStringRight tg xi ((<+>) yi zi)) N 
  ==. N 
  ==. map (shiftStringRight tg ((<+>) xi yi) zi) N 
  *** QED  
mapLenFusion tg xi yi zi (C i is)  
  =   map (shiftStringRight tg xi ((<+>) yi zi)) (map (shiftStringRight tg yi zi) (C i is))
  ==. map (shiftStringRight tg xi ((<+>) yi zi)) (shiftStringRight tg yi zi i `C` map (shiftStringRight tg yi zi) is)
  ==. shiftStringRight tg xi ((<+>) yi zi) (shiftStringRight tg yi zi i) `C` (map (shiftStringRight tg xi ((<+>) yi zi)) (map (shiftStringRight tg yi zi) is))
  ==. shiftStringRight tg ((<+>) xi yi) zi i `C` (map (shiftStringRight tg xi ((<+>) yi zi)) (map (shiftStringRight tg yi zi) is))
  ==. shiftStringRight tg ((<+>) xi yi) zi i `C` (map (shiftStringRight tg ((<+>) xi yi) zi) is)
       ? mapLenFusion tg xi yi zi is 
  ==. map (shiftStringRight tg ((<+>) xi yi) zi) (C i is)
  *** QED  
