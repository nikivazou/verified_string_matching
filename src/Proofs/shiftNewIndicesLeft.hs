#define IncludedshiftNewIndicesLeft
#ifdef IncludedmapCastId
#else  
#include "../Proofs/mapCastId.hs"   
#endif

{-@ shiftNewIndicesLeft
  :: xi:RString 
  -> yi:RString 
  -> zi:RString 
  -> tg:{RString | stringLen tg <= stringLen yi } 
  -> {  makeNewIndices xi (yi <+> zi) tg == map (castGoodIndexRight tg (xi <+> yi) zi) (makeNewIndices xi yi tg)}
  @-}

shiftNewIndicesLeft :: RString -> RString -> RString -> RString -> Proof
shiftNewIndicesLeft xi yi zi tg
  | stringLen tg < 2 
  =   makeNewIndices xi (yi <+> zi) tg 
  ==. N
  ==. makeNewIndices xi yi tg 
  ==. map (castGoodIndexRight tg (xi <+> yi) zi) (makeNewIndices xi yi tg)
      ?mapCastId tg (xi <+> yi) zi (makeNewIndices xi yi tg)
  *** QED 
  | otherwise
  =   makeNewIndices xi (yi <+> zi) tg 
  ==. makeIndices (xi <+> (yi <+> zi)) tg 
                   (maxInt (stringLen xi - (stringLen tg-1)) 0)
                   (stringLen xi - 1)
  ==. makeIndices ((xi <+> yi) <+> zi) tg 
                   (maxInt (stringLen xi - (stringLen tg-1)) 0)
                   (stringLen xi - 1)
     ?stringAssoc xi yi zi 
  ==. makeIndices (xi <+> yi) tg 
                  (maxInt (stringLen xi - (stringLen tg-1)) 0)
                  (stringLen xi - 1)                
      ?concatmakeNewIndices (maxInt (stringLen xi - (stringLen tg-1)) 0) (stringLen xi - 1) tg (xi <+> yi) zi 
  ==. makeNewIndices xi yi tg 
  ==. map (castGoodIndexRight tg (xi <+> yi) zi) (makeNewIndices xi yi tg)
      ?mapCastId tg (xi <+> yi) zi (makeNewIndices xi yi tg)
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
      ?isGoodIndexConcatString input input' target lo  
  *** QED 
  | lo == hi
  =  makeIndices input target lo hi 
  ==. makeIndices input target (lo+1) hi
  ==. N
  ==. makeIndices (input <+> input') target (lo+1) hi
  ==. makeIndices (input <+> input') target lo hi
      ?isGoodIndexConcatString input input' target lo  
  *** QED 
concatmakeNewIndices lo hi target input input' 
  | isGoodIndex input target lo
  =   makeIndices input target lo hi
  ==. lo `C` (makeIndices input target (lo + 1) hi)
  ==. lo `C` (makeIndices (input <+> input') target (lo + 1) hi)
      ? concatmakeNewIndices (lo+1) hi target input input'
  ==. makeIndices  (input <+> input') target lo hi
      ?isGoodIndexConcatString input input' target lo  
  *** QED 
  | otherwise 
  =   makeIndices input target lo hi
  ==. makeIndices input target (lo + 1) hi
  ==. makeIndices (input <+> input') target (lo + 1) hi
      ?concatmakeNewIndices (lo+1) hi target input input'
  ==. makeIndices  (input <+> input') target lo hi
      ? isGoodIndexConcatString input input' target lo  
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
  ==. (subString (input <+> input') i (stringLen tg)  == tg  
      && i + stringLen tg <= stringLen input 
      && 0 <= i)   
      ? (subStringConcatBack input input' (stringLen tg) i *** QED )
  ==. (subString (input <+> input') i (stringLen tg)  == tg  
      && i + stringLen tg <= stringLen (input <+> input') 
      && 0 <= i)   
      ? (((stringLen input <= stringLen (input <+> input') *** QED ) &&& (concatLen input input') *** QED))
  ==. isGoodIndex (input <+> input') tg i 
  *** QED 
