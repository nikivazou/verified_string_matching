#define IncludedconcatMakeIndices

{-@ automatic-instances concatMakeIndices @-}

{-@ concatMakeIndices
  :: lo:INat -> hi:Integer
  -> target: RString
  -> input : {RString | hi + stringLen target <= stringLen input } 
  -> input': RString   
  -> { makeIndices (input <+> input') target lo hi == makeIndices input target lo hi }
  / [hi - lo]  @-}
concatMakeIndices :: Integer -> Integer -> RString -> RString -> RString  -> Proof
concatMakeIndices lo hi target input input'
  | hi < lo 
  =  trivial 

concatMakeIndices lo hi target input input'
  | lo == hi
  =  makeIndices input target lo hi 
  ==. makeIndices input target (lo+1) hi
  ==. makeIndices (input <+> input') target (lo+1) hi
  ==. makeIndices (input <+> input') target lo hi
      ?isGoodIxConcatBack input input' target lo  
  *** QED 
concatMakeIndices lo hi target input input' 
  |   isGoodIndex input target lo
  =   concatMakeIndices (lo+1) hi target input input'
  &&& isGoodIxConcatBack input input' target lo  
concatMakeIndices lo hi target input input'
  =   concatMakeIndices (lo+1) hi target input input'
  &&& isGoodIxConcatBack input input' target lo  
 

{- FAILS  automatic-instances isGoodIxConcatBack @-}

{-@ isGoodIxConcatBack 
  :: input:RString -> input':RString -> tg:RString -> i:{Integer | i + stringLen tg <= stringLen input }
  -> {((isGoodIndex input tg i) <=> isGoodIndex (input <+> input') tg i)
     } @-}
isGoodIxConcatBack :: RString -> RString -> RString -> Integer -> Proof 
isGoodIxConcatBack input input' tg i 
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

