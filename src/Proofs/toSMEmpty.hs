#define IncludedtoSMEmpty

{-@ toSMEmpty :: SM target -> x:{RString | stringLen x == 0} -> {toSM x == mempty} @-}
toSMEmpty :: forall (target :: Symbol). (KnownSymbol target) =>  SM target ->  RString -> Proof
toSMEmpty _ x
  =   toSM x 
  ==. SM x (makeSMIndices x tg)
  ==. SM x (makeIndices x tg 0 (stringLen x -1))
       ? stringEmpProp x 
  ==. SM stringEmp N 
  ==. (mempty :: SM target)
  *** QED 
  where 
    tg  = fromString (symbolVal (Proxy :: Proxy target))
