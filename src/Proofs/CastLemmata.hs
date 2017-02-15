{-@ castAppend :: target:RString -> input:RString -> x:RString 
     -> is1:List (GoodIndex input target) 
     -> is2:List (GoodIndex input target) -> 
   {map (castGoodIndexRight target input x) (append is1 is2) == append (map (castGoodIndexRight target input x) is1) (map (castGoodIndexRight target input x) is2)}
    @-}
castAppend :: RString -> RString -> RString -> List Int -> List Int -> Proof 
castAppend target input x is1 is2 
  =   mapAppend (castGoodIndexRight target input x) is1 is2
  *** QED 
