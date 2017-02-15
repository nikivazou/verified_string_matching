#ifdef IncludedmakeNewIndicesNullLeft
#else  
#include "../Proofs/makeNewIndicesNullLeft.hs"   
#endif

#ifdef IncludedmakeNewIndicesNullRight
#else  
#include "../Proofs/makeNewIndicesNullRight.hs"   
#endif

#ifdef IncludedmapShiftZero
#else  
#include "../Proofs/mapShiftZero.hs"   
#endif

#ifdef IncludedmakeIndicesNull
#else  
#include "../Proofs/makeIndicesNull.hs"   
#endif

#ifdef IncludedcatIndices
#else  
#include "../Proofs/catIndices.hs"   
#endif

#ifdef IncludedmergeIndices
#else  
#include "../Proofs/mergeIndices.hs"   
#endif

#ifdef IncludedmapCastId
#else  
#include "../Proofs/mapCastId.hs"   
#endif
-------------------------------------------------------------------------------
----------  Lemmata on Shifting Indices ---------------------------------------
-------------------------------------------------------------------------------

{-@ shiftNewIndices
  :: xi:RString 
  -> yi:RString 
  -> zi:RString 
  -> tg:{RString | stringLen yi < stringLen tg  } 
  -> {  append (makeNewIndices xi (yi <+> zi) tg) (map (shiftStringRight tg xi (yi <+> zi)) (makeNewIndices yi zi tg)) 
     == append (map (castGoodIndexRight tg (xi <+> yi) zi) (makeNewIndices xi yi tg)) (makeNewIndices (xi <+> yi) zi tg)
     }
  @-}
shiftNewIndices :: RString -> RString -> RString -> RString -> Proof
shiftNewIndices xi yi zi tg 
  | stringLen tg < 2 
  =   append (makeNewIndices xi yzi tg) (map (shiftStringRight tg xi yzi) (makeNewIndices yi zi tg)) 
  ==. append N (map (shiftStringRight tg xi yzi) N) 
  ==. map (shiftStringRight tg xi yzi) N 
  ==. N 
  ==. append N N
  ==. append (makeNewIndices xi yi tg) (makeNewIndices xyi zi tg)
  ==. append (map (castGoodIndexRight tg xyi zi) (makeNewIndices xi yi tg)) (makeNewIndices xyi zi tg)
       ? mapCastId tg xyi zi (makeNewIndices xi yi tg)
  *** QED   
  where
    yzi = yi <+> zi
    xyi = xi <+> yi
    xyziL = xyi <+> zi


shiftNewIndices xi yi zi tg 
  | stringLen xi == 0 
  =   append (makeNewIndices xi yzi tg) 
                  (map (shiftStringRight tg xi yzi) (makeNewIndices yi zi tg))
  ==. append (makeNewIndices stringEmp yzi tg) 
                  (map (shiftStringRight tg xi yzi) (makeNewIndices yi zi tg))
  ? stringEmpProp xi 
  ==. append (makeNewIndices stringEmp yzi tg) 
                  (map (shiftStringRight tg xi yzi) (makeNewIndices yi zi tg))
  ? makeNewIndicesNullRight yzi tg
  ==. append N
                  (map (shiftStringRight tg xi yzi) (makeNewIndices yi zi tg))
  ==. map (shiftStringRight tg xi yzi) (makeNewIndices yi zi tg)
       ? stringEmpProp xi
  ==. map (shiftStringRight tg stringEmp yzi) (makeNewIndices yi zi tg)
      ? mapShiftZero tg yzi (makeNewIndices yi zi tg)
  ==. makeNewIndices yi zi tg
  ==. makeNewIndices xyi zi tg
        ? concatEmpLeft xi yi 
  ==. append N (makeNewIndices xyi zi tg)
  ==. append (makeNewIndices stringEmp yi tg) (makeNewIndices xyi zi tg)
       ? makeNewIndicesNullRight yi tg
  ==. append (makeNewIndices xi yi tg) (makeNewIndices xyi zi tg)
      ? stringEmpProp xi
  ==. append (map (castGoodIndexRight tg xyi zi) (makeNewIndices xi yi tg)) (makeNewIndices xyi zi tg)
       ? mapCastId tg xyi zi (makeNewIndices xi yi tg)
  *** QED 

  | stringLen yi == 0 
  =   append (makeNewIndices xi yzi tg) 
            (map (shiftStringRight tg xi yzi) (makeNewIndices yi zi tg))
  ==. append (makeNewIndices xi zi tg) 
             (map (shiftStringRight tg xi yzi) (makeNewIndices yi zi tg))
      ?(stringEmpProp yi &&& concatEmpLeft yi zi)
  ==. append (makeNewIndices xi zi tg) 
             (map (shiftStringRight tg xi zi) (makeNewIndices stringEmp zi tg))
  ==. append (makeNewIndices xi zi tg) 
             (map (shiftStringRight tg xi (stringEmp <+> zi)) N)
      ?makeNewIndicesNullRight zi tg 
  ==. append (makeNewIndices xi zi tg) N
  ==. makeNewIndices xi zi tg 
      ?listLeftId (makeNewIndices xi zi tg)
  ==. makeNewIndices xyi zi tg
      ?concatEmpRight xi yi
  ==. append N (makeNewIndices xyi zi tg)
  ==. append (makeNewIndices xi stringEmp tg) (makeNewIndices xyi zi tg)
      ?makeNewIndicesNullLeft xi tg 
  ==. append (makeNewIndices xi yi tg) (makeNewIndices xyi zi tg)
  ==. append (map (castGoodIndexRight tg xyi zi) (makeNewIndices xi yi tg)) (makeNewIndices xyi zi tg)
      ? (stringEmpProp yi &&& mapCastId tg xyi zi (makeNewIndices xi yi tg))
  *** QED 
  | stringLen yi - stringLen tg == - 1 
  =   append (makeNewIndices xi yzi tg) 
             (map (shiftStringRight tg xi yzi) (makeNewIndices yi zi tg)) 
  ==. append (makeIndices xyziR tg loxi hixi) 
             (map (shiftStringRight tg xi yzi) (makeIndices yzi tg loyi hiyi))
  ==. append (makeIndices xyziR tg loxi hixi) 
             (makeIndices xyziR tg midxyi hixyi)
      ?shiftIndicesRight loyi hiyi xi yzi tg 
  ==. append (makeIndices xyziL tg loxi hixi) 
             (makeIndices xyziL tg midxyi hixyi)
      ?concatStringAssoc xi yi zi 
  ==. append (append (makeIndices xyziR tg loxi midxi) 
                     (makeIndices xyziR tg (midxi+1) hixi))
             (makeIndices xyziR tg midxyi hixyi)
      ?mergeIndices xyziL tg loxi midxi hixi  
  ==. append (append (makeIndices xyziR tg loxi midxi) N)
             (makeIndices xyziR tg midxyi hixyi)
  ==. append (makeIndices xyziR tg loxi midxi)
             (makeIndices xyziR tg midxyi hixyi)
      ?listLeftId (makeIndices xyziR tg loxi midxi) 
  ==. append (makeIndices xyi tg loxi hixi)
             (makeIndices xyziR tg midxyi hixyi)
      ?catIndices xyi zi tg loxi hixi 
  ==. append (makeIndices xyi  tg loxi  hixi) 
             (makeIndices xyziL tg loxyi hixyi)
  ==. append (makeNewIndices xi yi tg) (makeNewIndices xyi zi tg)
  ==. append (map (castGoodIndexRight tg xyi zi) (makeNewIndices xi yi tg)) (makeNewIndices xyi zi tg)
      ?mapCastId tg xyi zi (makeNewIndices xi yi tg)
 *** QED 
  | 0 <= stringLen xi + stringLen yi - stringLen tg
  =   append (makeNewIndices xi yzi tg) 
             (map (shiftStringRight tg xi yzi) (makeNewIndices yi zi tg)) 
  ==. append (makeIndices xyziR tg loxi hixi) 
             (map (shiftStringRight tg xi yzi) (makeIndices yzi tg loyi hiyi))
  ==. append (makeIndices xyziR tg loxi hixi) 
             (makeIndices xyziR tg midxyi hixyi)
      ?shiftIndicesRight loyi hiyi xi yzi tg 
  ==. append (makeIndices xyziL tg loxi hixi) 
             (makeIndices xyziL tg midxyi hixyi)
      ?concatStringAssoc xi yi zi 
  ==. append (append (makeIndices xyziR tg loxi midxi) 
                     (makeIndices xyziR tg (midxi+1) hixi))
             (makeIndices xyziR tg midxyi hixyi)
      ?mergeIndices xyziL tg loxi midxi hixi  
  ==. append  (makeIndices xyziL tg loxi midxi) 
      (append (makeIndices xyziL tg (midxi+1) hixi)
              (makeIndices xyziL tg midxyi hixyi))
      ?listAssoc (makeIndices xyziR tg loxi midxi) (makeIndices xyziR tg (midxi+1) hixi) (makeIndices xyziR tg midxyi hixyi)
  ==. append  (makeIndices xyziL tg loxi midxi) 
              (makeIndices xyziL tg (midxi+1) hixyi)
      ?mergeIndices xyziL tg (midxi+1) hixi hixyi
  ==. append  (makeIndices xyi tg loxi hixi) 
              (makeIndices xyziL tg (midxi+1) hixyi)
      ?catIndices xyi zi tg loxi hixi 
  ==. append (makeIndices xyi  tg loxi  hixi) 
             (makeIndices xyziL tg loxyi hixyi)
  ==. append (makeNewIndices xi yi tg) (makeNewIndices xyi zi tg)
  ==. append (map (castGoodIndexRight tg xyi zi) (makeNewIndices xi yi tg)) (makeNewIndices xyi zi tg)
      ?mapCastId tg xyi zi (makeNewIndices xi yi tg)
 *** QED 

  | stringLen xi + stringLen yi < stringLen tg
  =   append (makeNewIndices xi yzi tg) 
             (map (shiftStringRight tg xi yzi) (makeNewIndices yi zi tg)) 
  ==. append (makeIndices xyziR tg loxi hixi) 
             (map (shiftStringRight tg xi yzi) (makeIndices yzi tg loyi hiyi))
  ==. append (makeIndices xyziR tg loxi hixi) 
             (makeIndices xyziR tg midxyi hixyi)
      ?shiftIndicesRight loyi hiyi xi yzi tg 
  ==. append (makeIndices xyziL tg loxi hixi) 
             (makeIndices xyziL tg midxyi hixyi)
      ?concatStringAssoc xi yi zi 
  ==. makeIndices xyziL tg 0 (stringLen xyi - 1)
      ?mergeIndices xyziL tg  loxi hixi hixyi
  ==. append N (makeIndices xyziL tg 0 hixyi)
  ==. append (makeIndices xyi  tg loxi  hixi) 
             (makeIndices xyziL tg loxyi hixyi)
      ? makeIndicesNull xyi tg 0 (stringLen xi -1)
  ==. append (makeNewIndices xi yi tg) (makeNewIndices xyi zi tg)
  ==. append (map (castGoodIndexRight tg xyi zi) (makeNewIndices xi yi tg)) (makeNewIndices xyi zi tg)
       ? mapCastId tg xyi zi (makeNewIndices xi yi tg)
  *** QED 
  where
    xyziR = xi <+> (yi <+> zi)
    xyziL = xyi <+> zi
    yzi = yi <+> zi
    xyi = xi <+> yi
    
    midxyi = maxInt (stringLen xi + stringLen yi - stringLen tg + 1) (stringLen xi) 
    midxi  = stringLen xi + stringLen yi - stringLen tg 

    loyi  = maxInt (stringLen yi - stringLen tg + 1) 0
    loxi  = maxInt (stringLen xi - stringLen tg + 1) 0
    loxyi = maxInt (stringLen xyi - stringLen tg + 1) 0 

    hiyi = stringLen yi - 1
    hixi = stringLen xi - 1

    hixyi = stringLen xi + hiyi

