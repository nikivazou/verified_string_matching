#define IncludedshiftNewIndicesRight

{-@ shiftNewIndicesRight
  :: xi:RString 
  -> yi:RString 
  -> zi:RString 
  -> tg:{RString | stringLen tg <= stringLen yi } 
  -> { map (shiftStringRight tg xi (yi <+> zi)) (makeNewIndices yi zi tg) == makeNewIndices (xi <+> yi) zi tg }
  @-}
shiftNewIndicesRight :: RString -> RString -> RString -> RString -> Proof
shiftNewIndicesRight xi yi zi tg
  | stringLen tg < 2 
  =   makeNewIndices (xi <+> yi) zi tg 
  ==. N
  ==. map (shiftStringRight tg xi (yi <+> zi)) N
  ==. map (shiftStringRight tg xi (yi <+> zi)) (makeNewIndices yi zi tg)
  *** QED 
shiftNewIndicesRight xi yi zi tg
  =   makeNewIndices (xi <+> yi) zi tg  
  ==. makeIndices ((xi <+> yi) <+> zi) tg 
                   (maxInt (stringLen (xi <+> yi) - (stringLen tg - 1)) 0)
                   (stringLen (xi <+> yi) - 1 )
  ==. makeIndices (xi <+> (yi <+> zi)) tg 
                   (stringLen xi + stringLen yi - stringLen tg + 1)
                   (stringLen xi + stringLen yi - 1 )
      ?stringAssoc xi yi zi
  ==. map (shiftStringRight tg xi (yi <+> zi)) (makeIndices (yi <+> zi) tg (stringLen yi - stringLen tg + 1) (stringLen yi - 1))
      ?shiftIndicesRight (stringLen yi - stringLen tg + 1)
                         (stringLen yi - 1)
                         xi 
                         (yi <+> zi)
                         tg 
  ==. map (shiftStringRight tg xi (yi <+> zi)) 
               (makeIndices (yi <+> zi) tg 
                            (maxInt (stringLen yi - (stringLen tg -1)) 0)
                            (stringLen yi -1))
  ==. map (shiftStringRight tg xi (yi <+> zi)) 
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
  ==. makeIndices (x <+> input) target (stringLen x + lo) (stringLen x + hi)
  *** QED 
  | lo == hi, isGoodIndex input target lo 
  =   map (shiftStringRight target x input) (makeIndices input target lo hi)
  ==. map (shiftStringRight target x input) (lo `C` makeIndices input target (lo+1) hi)
  ==. map (shiftStringRight target x input) (lo `C` N)
  ==. (shiftStringRight target x input lo) `C` (map (shiftStringRight target x input) N)
  ==. (stringLen x + lo) `C` N
  ==. (stringLen x + lo) `C` makeIndices (x <+> input) target (stringLen x + lo + 1) (stringLen x + hi)
  ==. makeIndices (x <+> input) target (stringLen x + lo) (stringLen x + hi)
     ? isGoodIndexConcatFront input x target lo  
  *** QED 
  | lo == hi
  =   map (shiftStringRight target x input) (makeIndices input target lo hi)
  ==. map (shiftStringRight target x input) (makeIndices input target (lo+1) hi)
  ==. map (shiftStringRight target x input) N
  ==. N
  ==. makeIndices (x <+> input) target (stringLen x + lo + 1) (stringLen x + hi)
  ==. makeIndices (x <+> input) target (stringLen x + lo) (stringLen x + hi)
     ? isGoodIndexConcatFront input x target lo 
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
      ? isGoodIndexConcatFront input x target lo 
  *** QED 
  | otherwise
  =   map (shiftStringRight target x input) (makeIndices input target lo hi)
  ==. map (shiftStringRight target x input) (makeIndices input target (lo + 1) hi)
  ==. makeIndices ((<+>) x input) target (stringLen x + (lo+1)) (stringLen x + hi)
      ? shiftIndicesRight (lo+1) hi x input target
  ==. makeIndices ((<+>) x input) target (stringLen x + lo) (stringLen x + hi)
     ? isGoodIndexConcatFront input x target lo 
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
      && (stringLen input' + i) + stringLen tg <= stringLen (input' <+> input) 
      && 0 <= i)  
  ==. (subString (input' <+> input) (stringLen input' + i) (stringLen tg)  == tg  
      && (stringLen input' + i) + stringLen tg <= stringLen (input' <+> input) 
      && 0 <= (stringLen input' + i))  
      ? (subStringConcatFront input input' (stringLen tg) i *** QED)
  ==. isGoodIndex (input' <+> input) tg (stringLen input' + i) 
  *** QED 
