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

-------------------------------------------------------------------------------
----------  Lemmata on Shifting Indices ---------------------------------------
-------------------------------------------------------------------------------

{-@ shiftNewIndices
  :: xi:RString 
  -> yi:RString 
  -> zi:RString 
  -> tg:{RString | stringLen yi < stringLen tg  } 
  -> {  append (makeNewIndices xi (yi <+> zi) tg) (map (shiftStringRight tg xi (yi <+> zi)) (makeNewIndices yi zi tg)) == append (map (castGoodIndexRight tg (xi <+> yi) zi) (makeNewIndices xi yi tg)) (makeNewIndices (xi <+> yi) zi tg)
     }
  @-}
shiftNewIndices :: RString -> RString -> RString -> RString -> Proof
shiftNewIndices xi yi zi tg 
  | stringLen tg < 2 
  =   append (makeNewIndices xi ((<+>) yi zi) tg) (map (shiftStringRight tg xi ((<+>) yi zi)) (makeNewIndices yi zi tg)) 
  ==. append N (map (shiftStringRight tg xi ((<+>) yi zi)) N) 
  ==. map (shiftStringRight tg xi ((<+>) yi zi)) N 
  ==. N 
  ==. append N N
  ==. append (makeNewIndices xi yi tg) (makeNewIndices ((<+>) xi yi) zi tg)
  ==. append (map (castGoodIndexRight tg (xi <+> yi) zi) (makeNewIndices xi yi tg)) (makeNewIndices ((<+>) xi yi) zi tg)
       ? mapCastId tg (xi <+> yi) zi (makeNewIndices xi yi tg)
  *** QED 

shiftNewIndices xi yi zi tg 
  | stringLen xi == 0 
  =   append (makeNewIndices xi ((<+>) yi zi) tg) 
                  (map (shiftStringRight tg xi ((<+>) yi zi)) (makeNewIndices yi zi tg))
  ==. append (makeNewIndices stringEmp ((<+>) yi zi) tg) 
                  (map (shiftStringRight tg xi ((<+>) yi zi)) (makeNewIndices yi zi tg))
  ? stringEmpProp xi 
  ==. append (makeNewIndices stringEmp ((<+>) yi zi) tg) 
                  (map (shiftStringRight tg xi ((<+>) yi zi)) (makeNewIndices yi zi tg))
  ? makeNewIndicesNullRight ((<+>) yi zi) tg
  ==. append N
                  (map (shiftStringRight tg xi ((<+>) yi zi)) (makeNewIndices yi zi tg))
  ==. map (shiftStringRight tg xi ((<+>) yi zi)) (makeNewIndices yi zi tg)
       ? stringEmpProp xi
  ==. map (shiftStringRight tg stringEmp ((<+>) yi zi)) (makeNewIndices yi zi tg)
      ? mapShiftZero tg ((<+>) yi zi) (makeNewIndices yi zi tg)
  ==. makeNewIndices yi zi tg
  ==. makeNewIndices ((<+>) xi yi) zi tg
        ? concatEmpLeft xi yi 
  ==. append N (makeNewIndices ((<+>) xi yi) zi tg)
  ==. append (makeNewIndices stringEmp yi tg) (makeNewIndices ((<+>) xi yi) zi tg)
       ? makeNewIndicesNullRight yi tg
  ==. append (makeNewIndices xi yi tg) (makeNewIndices ((<+>) xi yi) zi tg)
      ? stringEmpProp xi
  ==. append (map (castGoodIndexRight tg ((<+>) xi yi) zi) (makeNewIndices xi yi tg)) (makeNewIndices ((<+>) xi yi) zi tg)
       ? mapCastId tg (xi <+> yi) zi (makeNewIndices xi yi tg)
  *** QED 
  | stringLen yi == 0 
  =   append (makeNewIndices xi ((<+>) yi zi) tg) 
                  (map (shiftStringRight tg xi ((<+>) yi zi)) (makeNewIndices yi zi tg))
  ==. append (makeNewIndices xi zi tg) 
                  (map (shiftStringRight tg xi ((<+>) yi zi)) (makeNewIndices yi zi tg))
      ? (stringEmpProp yi &&& concatEmpLeft yi zi)
  ==. append (makeNewIndices xi zi tg) 
                  (map (shiftStringRight tg xi zi) (makeNewIndices stringEmp zi tg))
  ==. append (makeNewIndices xi zi tg) 
                  (map (shiftStringRight tg xi ((<+>) stringEmp zi)) N)
      ? makeNewIndicesNullRight zi tg 
  ==. append (makeNewIndices xi zi tg) 
                  N
  ==. makeNewIndices xi zi tg 
       ? appendNil (makeNewIndices xi zi tg)
  ==. makeNewIndices ((<+>) xi yi) zi tg
       ? concatEmpRight xi yi
  ==. append N (makeNewIndices ((<+>) xi yi) zi tg)
  ==. append (makeNewIndices xi stringEmp tg) (makeNewIndices ((<+>) xi yi) zi tg)
       ? makeNewIndicesNullLeft xi tg 
  ==. append (makeNewIndices xi yi tg) (makeNewIndices ((<+>) xi yi) zi tg)
  ==. append (map (castGoodIndexRight tg ((<+>) xi yi) zi) (makeNewIndices xi yi tg)) (makeNewIndices ((<+>) xi yi) zi tg)
       ? (stringEmpProp yi
       &&& mapCastId tg (xi <+> yi) zi (makeNewIndices xi yi tg))
  *** QED 
  | stringLen yi - stringLen tg == -1 
  = let minidx = maxInt (stringLen xi - stringLen tg + 1) 0 in 
      append (makeNewIndices xi ((<+>) yi zi) tg) 
                  (map (shiftStringRight tg xi ((<+>) yi zi)) (makeNewIndices yi zi tg)) 
  ==. append (makeIndices ((<+>) xi ((<+>) yi zi)) tg
                                (maxInt (stringLen xi - stringLen tg + 1) 0)
                                (stringLen xi -1)) 
                  (map (shiftStringRight tg xi ((<+>) yi zi)) 
                            (makeIndices ((<+>) yi zi) tg
                                          (maxInt (stringLen yi - stringLen tg +1) 0)
                                          (stringLen yi -1)
                            )) 
  ==. append (makeIndices ((<+>) xi ((<+>) yi zi)) tg
                                (maxInt (stringLen xi - stringLen tg + 1) 0)
                                (stringLen xi -1)) 
                  (map (shiftStringRight tg xi ((<+>) yi zi)) 
                            (makeIndices ((<+>) yi zi) tg
                                          (maxInt 0 0)
                                          (stringLen yi -1)
                            ))  
  ==. append (makeIndices ((<+>) xi ((<+>) yi zi)) tg
                                (maxInt (stringLen xi - stringLen tg + 1) 0)
                                (stringLen xi -1)) 
                  (map (shiftStringRight tg xi ((<+>) yi zi)) 
                            (makeIndices ((<+>) yi zi) tg
                                          0
                                          (stringLen yi -1)
                            )) 
  ==. append (makeIndices ((<+>) xi ((<+>) yi zi)) tg
                                minidx
                                (stringLen xi -1)) 
                  (makeIndices ((<+>) xi ((<+>) yi zi)) tg 
                                (stringLen xi) 
                                (stringLen xi + stringLen yi -1)) 
      ? shiftIndicesRight 0 (stringLen yi -1) xi ((<+>) yi zi) tg 
  ==. append (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                minidx
                                (stringLen xi -1)) 
                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg 
                                (stringLen xi) 
                                (stringLen xi + stringLen yi -1)) 
      ? concatStringAssoc xi yi zi 

  ==. append (append 

                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                minidx
                                (stringLen xi + stringLen yi - stringLen tg))

                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                (stringLen xi)
                                (stringLen xi -1))

                                ) 
                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg 
                                (stringLen xi)
                                (stringLen xi + stringLen yi -1)) 
      ? mergeIndices ((<+>) ((<+>) xi yi) zi) tg 
                     minidx -- maxInt (stringLen xi - stringLen tg + 1) 0
                     (stringLen xi -1)
                     (stringLen xi -1)
  ==. append (append 

                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                minidx
                                (stringLen xi + stringLen yi - stringLen tg))

                  N

                                ) 
                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg 
                                (stringLen xi)
                                (stringLen xi + stringLen yi -1)) 
  ==. append (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                minidx
                                (stringLen xi + stringLen yi - stringLen tg))
                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg 
                                (stringLen xi)
                                (stringLen xi + stringLen yi -1)) 
      ? appendNil (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                    minidx
                                    (stringLen xi + stringLen yi - stringLen tg))
  ==. append (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                minidx
                                (stringLen xi -1))

                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                ((stringLen xi))
                                (stringLen xi + stringLen yi -1))
  ==. append (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                minidx 
                                (stringLen ((<+>) xi yi)  - stringLen tg))

                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                (stringLen xi)
                                (stringLen xi + stringLen yi -1))

  ==. append (makeIndices ((<+>) xi yi) tg 
                                minidx
                                (stringLen xi-1)
                  ) 
                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                (stringLen xi)
                                (stringLen xi + stringLen yi  - 1)
                  )
      ? catIndices ((<+>) xi yi) zi tg minidx (stringLen xi-1)
  ==. append (makeIndices ((<+>) xi yi) tg 
                                minidx 
                                -- maxInt (stringLen xi - stringLen tg + 1) 0 && 2 <= stringLen tg
                                (stringLen xi-1)
                  ) 
                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                (stringLen xi)
                                (stringLen xi + stringLen yi  - 1)
                  )

  ==. append (makeIndices ((<+>) xi yi) tg 
                                minidx
                                (stringLen xi-1)
                  ) 
                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                (maxInt (stringLen xi) 0)
                                (stringLen xi + stringLen yi  - 1)
                  )


  ==. append (makeIndices ((<+>) xi yi) tg 
                                minidx
                                (stringLen xi-1)
                  ) 
                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                (maxInt (stringLen xi + stringLen yi - stringLen tg + 1) 0)
                                (stringLen xi + stringLen yi  - 1)
                  )

  ==. append (makeIndices ((<+>) xi yi) tg 
                                minidx
                                (stringLen xi-1)
                  ) 
                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                (maxInt (stringLen ((<+>) xi yi) - stringLen tg + 1) 0)
                                (stringLen ((<+>) xi yi) - 1)
                  )
  ==. append (makeIndices ((<+>) xi yi) tg 
                                (maxInt (stringLen xi - stringLen tg +1) 0)
                                (stringLen xi-1)
                  ) 
                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                (maxInt (stringLen ((<+>) xi yi) - stringLen tg + 1) 0)
                                (stringLen ((<+>) xi yi) - 1)
                  )
  ==. append (makeNewIndices xi yi tg) (makeNewIndices ((<+>) xi yi) zi tg)
  ==. append (map (castGoodIndexRight tg ((<+>) xi yi) zi) (makeNewIndices xi yi tg)) (makeNewIndices ((<+>) xi yi) zi tg)
       ? mapCastId tg (xi <+> yi) zi (makeNewIndices xi yi tg)
  *** QED 
  | 0 <= stringLen xi + stringLen yi - stringLen tg
  = let minidx = maxInt (stringLen xi - stringLen tg + 1) 0 in 
      append (makeNewIndices xi ((<+>) yi zi) tg) 
                  (map (shiftStringRight tg xi ((<+>) yi zi)) (makeNewIndices yi zi tg)) 
  ==. append (makeIndices ((<+>) xi ((<+>) yi zi)) tg
                                (maxInt (stringLen xi - stringLen tg + 1) 0)
                                (stringLen xi -1)) 
                  (map (shiftStringRight tg xi ((<+>) yi zi)) 
                            (makeIndices ((<+>) yi zi) tg
                                          (maxInt (stringLen yi - stringLen tg +1) 0)
                                          (stringLen yi -1)
                            )) 
  ==. append (makeIndices ((<+>) xi ((<+>) yi zi)) tg
                                minidx
                                (stringLen xi -1)) 
                  (map (shiftStringRight tg xi ((<+>) yi zi)) 
                            (makeIndices ((<+>) yi zi) tg
                                           0
                                          (stringLen yi -1)
                            )) 
  ==. append (makeIndices ((<+>) xi ((<+>) yi zi)) tg
                                minidx
                                (stringLen xi -1)) 
                  (makeIndices ((<+>) xi ((<+>) yi zi)) tg 
                                (stringLen xi) 
                                (stringLen xi + stringLen yi -1)) 
      ? shiftIndicesRight 0 (stringLen yi -1) xi ((<+>) yi zi) tg 
  ==. append (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                minidx
                                (stringLen xi -1)) 
                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg 
                                (stringLen xi) 
                                (stringLen xi + stringLen yi -1)) 
      ? concatStringAssoc xi yi zi 

  ==. append (append 

                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                minidx
                                (stringLen xi + stringLen yi - stringLen tg))

                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                (stringLen xi + stringLen yi - stringLen tg + 1)
                                (stringLen xi -1))

                                ) 
                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg 
                                (stringLen xi)
                                (stringLen xi + stringLen yi -1)) 
      ? mergeIndices ((<+>) ((<+>) xi yi) zi) tg 
                     minidx -- maxInt (stringLen xi - stringLen tg + 1) 0
                     (stringLen xi + stringLen yi - stringLen tg)
                     (stringLen xi -1)
  ==. append (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                minidx 
                                (stringLen xi + stringLen yi - stringLen tg))

                 (append

                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                (stringLen xi + stringLen yi - stringLen tg +1)
                                (stringLen xi -1))

                                
                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg 
                                (stringLen xi)
                                (stringLen xi + stringLen yi -1)) )
      ? appendAssoc
              (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                minidx
                                (stringLen xi + stringLen yi - stringLen tg))
              (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                (stringLen xi + stringLen yi - stringLen tg+1)
                                (stringLen xi -1))
              (makeIndices ((<+>) ((<+>) xi yi) zi) tg 
                                (stringLen xi)
                                (stringLen xi + stringLen yi -1))

  ==. append (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                minidx
                                (stringLen xi + stringLen yi - stringLen tg))

                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                ((stringLen xi + stringLen yi - stringLen tg+1))
                                (stringLen xi + stringLen yi -1))
     ? mergeIndices ((<+>) ((<+>) xi yi) zi) tg 
                  ((stringLen xi + stringLen yi - stringLen tg+1))
                  (stringLen xi-1)
                  (stringLen xi + stringLen yi -1)

  ==. append (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                minidx 
                                (stringLen ((<+>) xi yi)  - stringLen tg))

                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                (stringLen xi + stringLen yi - stringLen tg + 1)
                                (stringLen xi + stringLen yi -1))

  ==. append (makeIndices ((<+>) xi yi) tg 
                                minidx
                                (stringLen xi-1)
                  ) 
                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                (stringLen xi + stringLen yi - stringLen tg + 1)
                                (stringLen xi + stringLen yi  - 1)
                  )
      ? catIndices ((<+>) xi yi) zi tg minidx (stringLen xi-1)

  ==. append (makeIndices ((<+>) xi yi) tg 
                                minidx
                                (stringLen xi-1)
                  ) 
                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                (maxInt (stringLen xi + stringLen yi - stringLen tg + 1) 0)
                                (stringLen xi + stringLen yi  - 1)
                  )

  ==. append (makeIndices ((<+>) xi yi) tg 
                                minidx
                                (stringLen xi-1)
                  ) 
                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                (maxInt (stringLen ((<+>) xi yi) - stringLen tg + 1) 0)
                                (stringLen ((<+>) xi yi) - 1)
                  )
  ==. append (makeIndices ((<+>) xi yi) tg 
                                (maxInt (stringLen xi - stringLen tg +1) 0)
                                (stringLen xi-1)
                  ) 
                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                (maxInt (stringLen ((<+>) xi yi) - stringLen tg + 1) 0)
                                (stringLen ((<+>) xi yi) - 1)
                  )
  ==. append (makeNewIndices xi yi tg) (makeNewIndices ((<+>) xi yi) zi tg)
  ==. append (map (castGoodIndexRight tg ((<+>) xi yi) zi) (makeNewIndices xi yi tg)) (makeNewIndices ((<+>) xi yi) zi tg)
        ? mapCastId tg (xi <+> yi) zi (makeNewIndices xi yi tg)
 *** QED 
  | stringLen xi + stringLen yi < stringLen tg
  =   append (makeNewIndices xi ((<+>) yi zi) tg) 
                  (map (shiftStringRight tg xi ((<+>) yi zi)) (makeNewIndices yi zi tg)) 
  ==. append (makeIndices ((<+>) xi ((<+>) yi zi)) tg
                                (maxInt (stringLen xi - stringLen tg + 1) 0)
                                (stringLen xi -1)) 
                  (map (shiftStringRight tg xi ((<+>) yi zi)) 
                            (makeIndices ((<+>) yi zi) tg
                                          (maxInt (stringLen yi - stringLen tg +1) 0)
                                          (stringLen yi -1)
                            )) 
  ==. append (makeIndices ((<+>) xi ((<+>) yi zi)) tg
                                0
                                (stringLen xi -1)) 
                  (map (shiftStringRight tg xi ((<+>) yi zi)) 
                            (makeIndices ((<+>) yi zi) tg
                                           0
                                          (stringLen yi -1)
                            )) 
  ==. append (makeIndices ((<+>) xi ((<+>) yi zi)) tg
                                0
                                (stringLen xi -1)) 
                  (makeIndices ((<+>) xi ((<+>) yi zi)) tg 
                                (stringLen xi) 
                                (stringLen xi + stringLen yi -1)) 
      ? shiftIndicesRight 0 (stringLen yi -1) xi ((<+>) yi zi) tg 
  ==. append (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                0
                                (stringLen xi -1)) 
                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg 
                                (stringLen xi) 
                                (stringLen xi + stringLen yi -1)) 
      ? concatStringAssoc xi yi zi 

  ==. makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                0
                                (stringLen ((<+>) xi yi) - 1)
      ? mergeIndices ((<+>) ((<+>) xi yi) zi) tg 
                    0 
                    (stringLen xi-1) 
                    (stringLen ((<+>) xi yi) -1)

  ==. append N    (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                0
                                (stringLen ((<+>) xi yi) - 1)
                  )

  ==. append (makeIndices ((<+>) xi yi) tg 
                                0
                                (stringLen xi-1)
                  ) 
                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                0
                                (stringLen ((<+>) xi yi) - 1)
                  )
      ? makeIndicesNull ((<+>) xi yi) tg 0 (stringLen xi -1)
  ==. append (makeIndices ((<+>) xi yi) tg 
                                (maxInt (stringLen xi - stringLen tg +1) 0)
                                (stringLen xi-1)
                  ) 
                  (makeIndices ((<+>) ((<+>) xi yi) zi) tg
                                (maxInt (stringLen ((<+>) xi yi) - stringLen tg + 1) 0)
                                (stringLen ((<+>) xi yi) - 1)
                  )
  ==. append (makeNewIndices xi yi tg) (makeNewIndices ((<+>) xi yi) zi tg)
  ==. append (map (castGoodIndexRight tg ((<+>) xi yi) zi) (makeNewIndices xi yi tg)) (makeNewIndices ((<+>) xi yi) zi tg)
       ? mapCastId tg (xi <+> yi) zi (makeNewIndices xi yi tg)
  *** QED 