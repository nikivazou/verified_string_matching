#define IncludedshiftIndicesRight


{- automatic-instances shiftIndicesRight @-}
{-  AUTO INSTANCES FAILS -}
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
     ? isGoodIxConcatFront input x target lo  
  *** QED 
  | lo == hi
  =   map (shiftStringRight target x input) (makeIndices input target lo hi)
  ==. map (shiftStringRight target x input) (makeIndices input target (lo+1) hi)
  ==. map (shiftStringRight target x input) N
  ==. N
  ==. makeIndices (x <+> input) target (stringLen x + lo + 1) (stringLen x + hi)
  ==. makeIndices (x <+> input) target (stringLen x + lo) (stringLen x + hi)
     ? isGoodIxConcatFront input x target lo 
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
      ? isGoodIxConcatFront input x target lo 
  *** QED 
  | otherwise
  =   map (shiftStringRight target x input) (makeIndices input target lo hi)
  ==. map (shiftStringRight target x input) (makeIndices input target (lo + 1) hi)
  ==. makeIndices ((<+>) x input) target (stringLen x + (lo+1)) (stringLen x + hi)
      ? shiftIndicesRight (lo+1) hi x input target
  ==. makeIndices ((<+>) x input) target (stringLen x + lo) (stringLen x + hi)
     ? isGoodIxConcatFront input x target lo 
  *** QED 

{- automatic-instances isGoodIxConcatFront @-}
{-  AUTO INSTANCES FAILS -}

{-@ isGoodIxConcatFront 
  :: input:RString -> input':RString -> tg:RString -> i:Nat
  -> {(isGoodIndex input tg i) <=> (isGoodIndex (input' <+> input) tg (stringLen input' + i)) 
     } @-}
isGoodIxConcatFront :: RString -> RString -> RString -> Int -> Proof 
isGoodIxConcatFront input input' tg i 
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
