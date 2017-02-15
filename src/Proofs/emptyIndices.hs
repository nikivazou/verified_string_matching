#define IncludedemptyIndices

emptyIndices :: forall (target :: Symbol). (KnownSymbol target) => SM target -> List Int  -> Proof
{-@ emptyIndices :: mi:SM target
                 -> is:{List (GoodIndex (inputSM mi) target) | is == indicesSM mi && stringLen (inputSM mi) < stringLen target}
                 -> { is == N } @-}
emptyIndices (SM _ _) N 
  = trivial 
emptyIndices (SM _ _) (C _ _)
  = trivial 
