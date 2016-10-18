-------------------------------------------------------------------------------
----------  Lemmata on Shifting Indices ---------------------------------------
-------------------------------------------------------------------------------

mapLenFusion :: RString -> RString -> RString -> RString -> List Int -> Proof
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


{-@ shiftIndexesRight
  :: xi:RString 
  -> yi:RString 
  -> zi:RString 
  -> tg:{RString | stringLen tg <= stringLen yi } 
  -> { map (shiftStringRight tg xi (yi <+> zi)) (makeNewIndices yi zi tg) == makeNewIndices (xi <+> yi) zi tg }
  @-}
shiftIndexesRight :: RString -> RString -> RString -> RString -> Proof
shiftIndexesRight xi yi zi tg
  | stringLen tg < 2 
  =   makeNewIndices ((<+>) xi yi) zi tg 
  ==. N
  ==. map (shiftStringRight tg xi ((<+>) yi zi)) N
  ==. map (shiftStringRight tg xi ((<+>) yi zi)) (makeNewIndices yi zi tg)
  *** QED 
shiftIndexesRight xi yi zi tg
-- NV NV NV 
-- This is suspicious!!! it should require exactly the precondition 
-- || tg || <= || yi || 
--   | stringLen tg  <= stringLen yi + 1 
  =   makeNewIndices ((<+>) xi yi) zi tg  
  ==. makeIndices ((<+>) ((<+>) xi yi) zi) tg 
                   (maxInt (stringLen ((<+>) xi yi) - (stringLen tg -1)) 0)
                   (stringLen ((<+>) xi yi) - 1 )
  ==. makeIndices ((<+>) ((<+>) xi yi) zi) tg 
                   (stringLen ((<+>) xi yi) - (stringLen tg -1))
                   (stringLen ((<+>) xi yi) - 1 )
  ==. makeIndices ((<+>) ((<+>) xi yi) zi) tg 
                   (stringLen xi + stringLen yi - stringLen tg + 1)
                   (stringLen xi + stringLen yi - 1 )
  ==. makeIndices ((<+>) xi ((<+>) yi zi)) tg 
                   (stringLen xi + stringLen yi - stringLen tg + 1)
                   (stringLen xi + stringLen yi - 1 )
       ?concatStringAssoc xi yi zi
  ==. map (shiftStringRight tg xi ((<+>) yi zi)) (makeIndices ((<+>) yi zi) tg (stringLen yi - stringLen tg + 1) (stringLen yi - 1))
       ? shiftIndicesRight (stringLen yi - stringLen tg + 1)
                            (stringLen yi - 1)
                            xi 
                            ((<+>) yi zi)
                            tg 
  ==. map (shiftStringRight tg xi ((<+>) yi zi)) 
               (makeIndices ((<+>) yi zi) tg 
                             (maxInt (stringLen yi - (stringLen tg -1)) 0)
                             (stringLen yi -1))
  ==. map (shiftStringRight tg xi ((<+>) yi zi)) 
          (makeNewIndices yi zi tg)
  *** QED

{-@ shiftIndicesRight
  :: lo:Nat 
  -> hi:Int  
  -> x:RString 
  -> input:RString 
  -> target:RString
  -> { map (shiftStringRight target x input) (makeIndices input target lo hi) == makeIndices (x <+> input) target (stringLen x + lo) (stringLen x + hi) }
  / [if hi < lo then 0 else  hi-lo]
  @-}
shiftIndicesRight :: Int -> Int -> RString -> RString -> RString -> Proof
shiftIndicesRight lo hi x input target
  | hi < lo 
  =   map (shiftStringRight target x input) (makeIndices input target lo hi)
  ==. map (shiftStringRight target x input) N
  ==. N
  ==. makeIndices ((<+>) x input) target (stringLen x + lo) (stringLen x + hi)
  *** QED 
  | lo == hi, isGoodIndex input target lo 
  =   map (shiftStringRight target x input) (makeIndices input target lo hi)
  ==. map (shiftStringRight target x input) (lo `C` makeIndices input target (lo+1) hi)
  ==. map (shiftStringRight target x input) (lo `C` N)
  ==. (shiftStringRight target x input lo) `C` (map (shiftStringRight target x input) N)
  ==. (stringLen x + lo) `C` N
  ==. (stringLen x + lo) `C` makeIndices (x <+> input) target (stringLen x + lo + 1) (stringLen x + hi)
  ==. makeIndices (x <+> input) target (stringLen x + lo) (stringLen x + hi)
     ? isGoodIndexConcatFront input x target lo  -- ( => IsGoodIndex ((<+>) x input) target (stringLen x + lo))
  *** QED 
  | lo == hi
  =   map (shiftStringRight target x input) (makeIndices input target lo hi)
  ==. map (shiftStringRight target x input) (makeIndices input target (lo+1) hi)
  ==. map (shiftStringRight target x input) N
  ==. N
  ==. makeIndices (x <+> input) target (stringLen x + lo + 1) (stringLen x + hi)
  ==. makeIndices (x <+> input) target (stringLen x + lo) (stringLen x + hi)
     ? (isGoodIndexConcatFront input x target lo *** QED)
  *** QED 

shiftIndicesRight lo hi x input target
  | isGoodIndex input target lo
  =   map (shiftStringRight target x input) (makeIndices input target lo hi)
  ==. map (shiftStringRight target x input) (lo `C` makeIndices input target (lo+1) hi)
  ==. (shiftStringRight target x input lo) `C` (map (shiftStringRight target x input) (makeIndices input target (lo+1) hi))
  ==. (shift (stringLen x) lo) `C` (makeIndices ((<+>) x input) target (stringLen x + (lo+1)) (stringLen x + hi))
      ? shiftIndicesRight (lo+1) hi x input target
  ==. (stringLen x + lo) `C` (makeIndices ((<+>) x input) target (stringLen x + (lo+1)) (stringLen x + hi))
  ==. makeIndices ((<+>) x input) target (stringLen x + lo) (stringLen x + hi)
     ? (isGoodIndexConcatFront input x target lo *** QED)
  *** QED 
  | otherwise
  =   map (shiftStringRight target x input) (makeIndices input target lo hi)
  ==. map (shiftStringRight target x input) (makeIndices input target (lo + 1) hi)
  ==. makeIndices ((<+>) x input) target (stringLen x + (lo+1)) (stringLen x + hi)
      ? shiftIndicesRight (lo+1) hi x input target
  ==. makeIndices ((<+>) x input) target (stringLen x + lo) (stringLen x + hi)
     ? (isGoodIndexConcatFront input x target lo *** QED)
  *** QED 


{-@ shiftIndexesLeft
  :: xi:RString 
  -> yi:RString 
  -> zi:RString 
  -> tg:{RString | stringLen tg <= stringLen yi } 
  -> {  makeNewIndices xi (yi <+> zi) tg == map (castGoodIndexRight tg (xi <+> yi) zi) (makeNewIndices xi yi tg)}
  @-}
shiftIndexesLeft :: RString -> RString -> RString -> RString -> Proof
shiftIndexesLeft xi yi zi tg
  | stringLen tg < 2 
  =   makeNewIndices xi ((<+>) yi zi) tg 
  ==. N
  ==. makeNewIndices xi yi tg 
  ==. map (castGoodIndexRight tg ((<+>) xi yi) zi) (makeNewIndices xi yi tg)
      ? mapCastId tg (xi <+> yi) zi (makeNewIndices xi yi tg)
  *** QED 
  | otherwise
  =   makeNewIndices xi ((<+>) yi zi) tg 
  ==. makeIndices ((<+>) xi ((<+>) yi zi)) tg 
                   (maxInt (stringLen xi - (stringLen tg-1)) 0)
                   (stringLen xi - 1)
  ==. makeIndices ((<+>) ((<+>) xi yi) zi) tg 
                   (maxInt (stringLen xi - (stringLen tg-1)) 0)
                   (stringLen xi - 1)
     ?concatStringAssoc xi yi zi 
  ==. makeIndices ((<+>) xi yi) tg 
                   (maxInt (stringLen xi - (stringLen tg-1)) 0)
                   (stringLen xi - 1)                
      ? concatmakeNewIndices (maxInt (stringLen xi - (stringLen tg-1)) 0) (stringLen xi - 1) tg ((<+>) xi yi) zi 
  ==. makeNewIndices xi yi tg 
  ==. map (castGoodIndexRight tg ((<+>) xi yi) zi) (makeNewIndices xi yi tg)
      ? mapCastId tg (xi <+> yi) zi (makeNewIndices xi yi tg)
  *** QED 

{-@ concatmakeNewIndices
  :: lo:Nat -> hi:Int
  -> target: RString
  -> input : {RString | hi + stringLen target <= stringLen input } 
  -> input': RString   
  -> {  makeIndices (input <+> input') target lo hi == makeIndices input target lo hi }
  / [hi - lo]  @-}
concatmakeNewIndices :: Int -> Int -> RString -> RString -> RString  -> Proof
concatmakeNewIndices lo hi target input input'
  | hi < lo 
  =   makeIndices input target lo hi
  ==. N
  ==. makeIndices (input <+> input') target lo hi 
  *** QED 
  | lo == hi, isGoodIndex input target lo
  =   makeIndices input target lo hi
  ==. lo `C` makeIndices input target (lo+1) hi
  ==. lo `C` N
  ==. lo `C` makeIndices (input <+> input') target (lo+1) hi
  ==. makeIndices (input <+> input') target lo hi 
      ? isGoodIndexConcatString input input' target lo  
  *** QED 
  | lo == hi
  =  makeIndices input target lo hi 
  ==. makeIndices input target (lo+1) hi
  ==. N
  ==. makeIndices (input <+> input') target (lo+1) hi
  ==. makeIndices (input <+> input') target lo hi
      ? isGoodIndexConcatString input input' target lo  
  *** QED 
concatmakeNewIndices lo hi target input input' 
  | isGoodIndex input target lo
  =   makeIndices input target lo hi
  ==. lo `C` (makeIndices input target (lo + 1) hi)
  ==. lo `C` (makeIndices ((<+>) input input') target (lo + 1) hi)
       ? concatmakeNewIndices (lo+1) hi target input input'
  ==. makeIndices  ((<+>) input input') target lo hi
      ? isGoodIndexConcatString input input' target lo  
  *** QED 
  | otherwise 
  =   makeIndices input target lo hi
  ==. makeIndices input target (lo + 1) hi
  ==. makeIndices ((<+>) input input') target (lo + 1) hi
       ? concatmakeNewIndices (lo+1) hi target input input'
  ==. makeIndices  ((<+>) input input') target lo hi
      ? isGoodIndexConcatString input input' target lo  
  *** QED 



{-@ isGoodIndexConcatFront 
  :: input:RString -> input':RString -> tg:RString -> i:Nat
  -> {(isGoodIndex input tg i) <=> (isGoodIndex (input' <+> input) tg (stringLen input' + i)) 
     } @-}
isGoodIndexConcatFront :: RString -> RString -> RString -> Int -> Proof 
isGoodIndexConcatFront input input' tg i 
  =   isGoodIndex input tg i 
  ==. (subString input i (stringLen tg)  == tg  
      && i + stringLen tg <= stringLen input 
      && 0 <= i)  
  ==. (subString input i (stringLen tg)  == tg  
      && (stringLen input' + i) + stringLen tg <= stringLen ((<+>) input' input) 
      && 0 <= i)  
  ==. (subString ((<+>) input' input) (stringLen input' + i) (stringLen tg)  == tg  
      && (stringLen input' + i) + stringLen tg <= stringLen ((<+>) input' input) 
      && 0 <= (stringLen input' + i))  
      ? (subStringConcatFront input input' (stringLen tg) i *** QED)
  ==. isGoodIndex ((<+>) input' input) tg (stringLen input' + i) 
  *** QED 


{-@ isGoodIndexConcatString 
  :: input:RString -> input':RString -> tg:RString -> i:{Int | i + stringLen tg <= stringLen input }
  -> {((isGoodIndex input tg i) <=> isGoodIndex (input <+>  input') tg i)
     } @-}
isGoodIndexConcatString :: RString -> RString -> RString -> Int -> Proof 
isGoodIndexConcatString input input' tg i 
  =   isGoodIndex input tg i 
  ==. (subString input i (stringLen tg)  == tg  
      && i + stringLen tg <= stringLen input
      && 0 <= i) 
  ==. (subString ((<+>) input input') i (stringLen tg)  == tg  
      && i + stringLen tg <= stringLen input 
      && 0 <= i)   
      ? (subStringConcatBack input input' (stringLen tg) i *** QED )
  ==. (subString ((<+>) input input') i (stringLen tg)  == tg  
      && i + stringLen tg <= stringLen ((<+>) input input') 
      && 0 <= i)   
      ? (((stringLen input <= stringLen ((<+>) input input') *** QED ) &&& (concatLen input input') *** QED))
  ==. isGoodIndex ((<+>) input input') tg i 
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
