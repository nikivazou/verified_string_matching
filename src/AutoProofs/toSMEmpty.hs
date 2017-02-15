#define IncludedtoSMEmpty

{-@ automatic-instances toSMEmpty @-}

{-@ toSMEmpty :: SM target -> x:{RString | stringLen x == 0} -> {toSM x == mempty} @-}
toSMEmpty :: forall (target :: Symbol). (KnownSymbol target) =>  SM target ->  RString -> Proof
toSMEmpty _ x
  = stringEmpProp x 
