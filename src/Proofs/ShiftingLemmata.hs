#ifdef IncludedmakeNewIndicesNullLeft
#else  
#include "../Proofs/makeNewIndicesNullLeft.hs"   
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
shiftNewIndices xi yi zi tg 
-- THIS ALWAYS HOLDS 
--   | stringLen yi + 1 <= stringLen tg
  | 0 <= stringLen xi + stringLen yi - stringLen tg
 --  , 0 < stringLen xi 
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

--   | stringLen yi + 1 <= stringLen tg
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
      ? smallInput ((<+>) xi yi) tg 0 (stringLen xi -1)
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


smallInput :: RString -> RString -> Int -> Int -> Proof  
{-@ smallInput :: input:RString -> target:{RString | stringLen input < stringLen target } -> lo:Nat -> hi:Int 
           -> {makeIndices input target lo hi == N } 
           / [hi -lo]
  @-}
smallInput input target lo hi 
  | hi < lo 
  = makeIndices input target lo hi 
  ==. N
  *** QED  
  | lo == hi, not (isGoodIndex input target lo)
  = makeIndices input target lo hi 
  ==. makeIndices input target (lo+1) hi
  ==. N 
  *** QED  
  | not (isGoodIndex input target lo)
  = makeIndices input target lo hi 
  ==. makeIndices input target (lo+1) hi
  ==. N ? smallInput input target (lo+1) hi 
  *** QED  

maxIndices :: RString -> RString -> Int -> Int -> Proof 
{-@ maxIndices 
  :: input:RString -> target:RString -> lo:{Nat | stringLen input < lo + stringLen target} -> hi:Int
  -> {makeIndices input target lo hi = N}
  / [hi - lo ] @-}
maxIndices input target lo hi 
  | hi < lo 
  =   makeIndices input target lo hi  
  ==. N
  *** QED 
  | lo == hi, not (isGoodIndex input target lo)
  =   makeIndices input target lo hi  
  ==. makeIndices input target (lo+1) hi  
  ==. N
  *** QED 
  | not (isGoodIndex input target lo)
  =   makeIndices input target lo hi
  ==. makeIndices input target (lo+1) hi
  ==. N 
  ==. makeIndices input target (lo+1) hi 
      ? maxIndices input target (lo+1) hi 
  *** QED 


mergeIndices :: RString -> RString -> Int -> Int -> Int -> Proof
{-@ mergeIndices 
  :: input:RString -> target:RString -> lo:Nat -> mid:{Int | lo <= mid} -> hi:{Int | mid <= hi} 
  -> {makeIndices input target lo hi == append (makeIndices input target lo mid) (makeIndices input target (mid+1) hi)} 
  / [mid] @-}
mergeIndices input target lo mid hi 
  | lo == mid, isGoodIndex input target lo 
  =   append (makeIndices input target lo mid) (makeIndices input target (mid+1) hi)
  ==. append (makeIndices input target lo lo)  (makeIndices input target (mid+1) hi)
  ==. append (lo `C` (makeIndices input target (lo+1) lo))  (makeIndices input target (mid+1) hi)
  ==. append (lo `C` N)  (makeIndices input target (mid+1) hi)
  ==. lo  `C` (append N  (makeIndices input target (lo+1) hi))
  ==. lo  `C` (makeIndices input target (lo+1) hi)
  ==. makeIndices input target lo hi
  *** QED 
  | lo == mid, not (isGoodIndex input target lo)
  =   append (makeIndices input target lo mid) (makeIndices input target (mid+1) hi)
  ==. append (makeIndices input target lo lo)  (makeIndices input target (mid+1) hi)
  ==. append (lo `C` makeIndices input target (lo+1) lo)  (makeIndices input target (mid+1) hi)
  ==. append (lo `C` N)  (makeIndices input target (mid+1) hi)
  ==. (append N  (makeIndices input target (lo+1) hi))
  ==. makeIndices input target lo hi
  *** QED 
  | lo < mid, not (isGoodIndex input target mid)
  =   makeIndices input target lo hi
  ==. append (makeIndices input target lo (mid-1)) 
                  (makeIndices input target mid hi)
       ? mergeIndices input target lo (mid-1) hi 

  ==. append (makeIndices input target lo (mid-1)) 
                  (makeIndices input target (mid+1) hi)

  ==. append (makeIndices input target lo mid) 
                  (makeIndices input target (mid+1) hi)
      ?makeNewIndicesBadLast input target lo mid
  *** QED 
  | lo < mid, isGoodIndex input target mid
  =   makeIndices input target lo hi
  ==. append (makeIndices input target lo (mid-1)) 
                  (makeIndices input target mid hi)
       ? mergeIndices input target lo (mid-1) hi 

  ==. append (makeIndices input target lo (mid-1)) 
                  (mid `C` makeIndices input target (mid+1) hi)


  ==. append (makeIndices input target lo (mid-1)) 
                  (mid `C` (append N (makeIndices input target (mid+1) hi)))

  ==. append (makeIndices input target lo (mid-1)) 
                  (append (C mid N) (makeIndices input target (mid+1) hi))

  ==. append (append (makeIndices input target lo (mid-1)) (C mid N)) 
                  (makeIndices input target (mid+1) hi)
      ? appendAssoc (makeIndices input target lo (mid-1)) (C mid N) (makeIndices input target (mid+1) hi)

  ==. append (makeIndices input target lo mid) 
                  (makeIndices input target (mid+1) hi)
      ?makeNewIndicesGoodLast input target lo mid
  *** QED 


makeNewIndicesGoodLast, makeNewIndicesBadLast 
  :: RString -> RString -> Int -> Int -> Proof 
{-@ makeNewIndicesGoodLast 
  :: input:RString -> target:RString -> lo:Nat -> hi:{Int | lo <= hi && (isGoodIndex input target hi)}
  -> {makeIndices input target lo hi == append (makeIndices input target lo (hi-1)) (C hi N)}
  / [hi - lo] @-}
makeNewIndicesGoodLast input target lo hi 
  | lo == hi, (isGoodIndex input target lo)
  =   makeIndices input target lo hi 
  ==. hi `C` makeIndices input target (lo+1) hi  
  ==. hi `C` N 
  ==. append (N) (C hi N)
  ==. append (makeIndices input target lo (hi-1)) (C hi N)
  *** QED 
  | not (isGoodIndex input target lo), isGoodIndex input target hi 
  =   makeIndices input target lo hi 
  ==. makeIndices input target (lo+1) hi
  ==. append (makeIndices input target (lo+1) (hi-1)) (C hi N)
       ? makeNewIndicesGoodLast input target (lo+1) hi  
  ==. append (makeIndices input target lo (hi-1)) (C hi N)
  *** QED 
  | isGoodIndex input target lo, isGoodIndex input target hi
  =   makeIndices input target lo hi 
  ==. lo `C` makeIndices input target (lo+1) hi
  ==. lo `C` (append (makeIndices input target (lo+1) (hi-1)) (C hi N))
       ? makeNewIndicesGoodLast input target (lo+1) hi  
  ==. (append (lo `C` makeIndices input target (lo+1) (hi-1)) (C hi N))
  ==. append (makeIndices input target lo (hi-1)) (C hi N)
  *** QED 

{-@ makeNewIndicesBadLast 
  :: input:RString -> target:RString -> lo:Nat -> hi:{Int | lo <= hi && (not (isGoodIndex input target hi))}
  -> {makeIndices input target lo hi == makeIndices input target lo (hi-1)}
  / [hi - lo + 1]
@-}
-- NV sweet proof 
makeNewIndicesBadLast input target lo hi 
  | lo == hi, not (isGoodIndex input target lo)
  =   makeIndices input target lo (hi-1) 
  ==. N 
  ==. makeIndices input target (lo+1) hi
  ==. makeIndices input target lo hi
  *** QED 
  | not (isGoodIndex input target lo), not (isGoodIndex input target hi) 
  =   makeIndices input target lo hi 
  ==. makeIndices input target (lo+1) hi
  ==. makeIndices input target (lo+1) (hi-1)
       ? makeNewIndicesBadLast input target (lo+1) hi   
  ==. makeIndices input target lo (hi-1)
  *** QED 
  | isGoodIndex input target lo , not (isGoodIndex input target hi) 
  =   makeIndices input target lo hi 
  ==. lo `C` makeIndices input target (lo+1) hi
  ==. lo `C` makeIndices input target (lo+1) (hi-1)
       ? makeNewIndicesBadLast input target (lo+1) hi   
  ==. makeIndices input target lo (hi-1)
  *** QED 


catIndices :: RString -> RString -> RString -> Int -> Int -> Proof 
{-@ catIndices 
     :: input:RString -> x:RString 
     -> target:{RString | 0 <= stringLen input - stringLen target + 1} 
     -> lo:{Nat | lo <= stringLen input - stringLen target } 
     -> hi:{Int | (stringLen input - stringLen target) <= hi}
     -> { makeIndices input target lo hi == makeIndices (input <+> x) target lo (stringLen input - stringLen target) }
  @-}
catIndices input x target lo hi 
  =   makeIndices input target lo hi
  ==. append (makeIndices input target lo (stringLen input - stringLen target))
                  (makeIndices input target (stringLen input - stringLen target + 1) hi)
       ? mergeIndices input target lo (stringLen input - stringLen target) hi
  ==. append (makeIndices input target lo (stringLen input - stringLen target))
                  N
       ? maxIndices input target (stringLen input - stringLen target + 1) hi
  ==. makeIndices input target lo (stringLen input - stringLen target)
       ? appendNil (makeIndices input target lo (stringLen input - stringLen target))
  ==. makeIndices ((<+>) input x) target lo (stringLen input - stringLen target)
       ? concatmakeNewIndices lo (stringLen input - stringLen target) target input x 
  *** QED 
