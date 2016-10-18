-------------------------------------------------------------------------------
----------  Indexing Structure Definition -------------------------------------
-------------------------------------------------------------------------------


{-@ symbolVal :: forall n proxy. KnownSymbol n => x:proxy n 
  -> {v:String | v == n && v == symbolVal x } @-}
{-@ measure symbolVal :: p n -> String @-}


data SM (target :: Symbol) where 
  SM :: RString       -- | input string
     -> (List Int)    -- | valid indices of target in input
     -> SM target
  deriving (Show)

{-@ data SM target 
  = SM { input   :: RString
       , indices :: List (GoodIndex input target)
       } @-}

{-@ type GoodIndex Input Target 
  = {i:Int | IsGoodIndex Input Target i }
  @-}

{-@ type GoodIndexTwo Input X Target 
  = {i:Int | (IsGoodIndex Input Target i) && (IsGoodIndex (Input <+> X) Target i) }
  @-}


{-@ predicate IsGoodIndex Input Target I
  =  (subString Input I (stringLen Target)  == Target)
  && (I + stringLen Target <= stringLen Input)
  && (0 <= I)
  @-}

{-@ measure indicesSM @-}
indicesSM (SM _ is) = is 

{-@ measure inputSM @-}
inputSM (SM i _) = i 

-------------------------------------------------------------------------------
----------  Creation of SM ----------------------------------------------------
-------------------------------------------------------------------------------


{-@ reflect toSM @-}
toSM :: forall (target :: Symbol). (KnownSymbol target) => RString -> SM target 
toSM input = SM input (makeSMIndices input tg) 
  where
    tg = fromString (symbolVal (Proxy :: Proxy target))


{-@ reflect makeSMIndices @-}
{-@ makeSMIndices :: input:RString -> target:RString -> List (GoodIndex input target) @-}
makeSMIndices :: RString -> RString -> List Int 
makeSMIndices input target = makeIndices input target  0 (stringLen input - 1)

-------------------------------------------------------------------------------
----------  Monoid Operators on SM --------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect mempty @-}
mempty :: forall (target :: Symbol). (KnownSymbol target) =>  SM target
mempty = SM stringEmp N

{-@ reflect <> @-}
(<>) :: forall (target :: Symbol).  (KnownSymbol target) => SM target -> SM target -> SM target
(SM i1 is1) <> (SM i2 is2)
  = SM (i1 <+> i2) (is1' `append` is `append` is2')
  where 
    tg   = fromString (symbolVal (Proxy :: Proxy target))
    is1' = map (castGoodIndexRight tg i1 i2) is1
    is   = makeNewIndices i1 i2 tg
    is2' = map (shiftStringRight tg i1 i2)   is2



{-@ reflect makeNewIndices @-}
{-@ makeNewIndices :: s1:RString -> s2:RString -> target:RString -> List (GoodIndex { s1 <+> s2} target) @-}
makeNewIndices :: RString -> RString -> RString -> List Int 
makeNewIndices s1 s2 target
  | stringLen target < 2 
  = N
  | otherwise
  = makeIndices ((<+>) s1 s2) target
                (maxInt (stringLen s1 - (stringLen target-1)) 0)
                (stringLen s1 - 1)

{-@ reflect maxInt @-}
maxInt :: Int -> Int -> Int 
maxInt x y = if x <= y then y else x 

{-@ reflect shift @-}
shift :: Int -> Int -> Int 
shift x y = x + y 

-- | Helpers 
{-@ reflect shiftStringRight @-}
shiftStringRight :: RString -> RString -> RString -> Int -> Int 
{-@ shiftStringRight :: target:RString -> left:RString -> right:RString -> i:GoodIndex right target 
  -> {v:(GoodIndex {left <+> right} target) | v == i + stringLen left } @-}
shiftStringRight target left right i 
  = cast (subStringConcatFront right left (stringLen target) i) (shift (stringLen left) i)

{-@ reflect castGoodIndexRight @-}
castGoodIndexRight :: RString -> RString -> RString -> Int -> Int  
{-@ castGoodIndexRight :: target:RString -> input:RString -> x:RString -> i:GoodIndex input target 
   -> {v:(GoodIndexTwo input x target)| v == i} @-}
castGoodIndexRight target input x i  = cast (subStringConcatBack input x (stringLen target) i) i


-------------------------------------------------------------------------------
----------  Indices' Generation -----------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect makeIndices @-}
makeIndices :: RString -> RString -> Int -> Int -> List Int 
{-@ makeIndices :: input:RString -> target:RString -> lo:Nat -> hi:Int -> List (GoodIndex input target) 
  / [hi - lo + 1] @-}
makeIndices input target lo hi 
  | hi < lo 
  = N
makeIndices input target lo hi
 | isGoodIndex input target lo 
 = lo `C` rest
 | otherwise
 = rest
 where
  rest = makeIndices input target (lo + 1) hi



{-@ reflect isGoodIndex @-}
isGoodIndex :: RString -> RString -> Int -> Bool 
{-@ isGoodIndex :: input:RString -> target:RString -> i:Int 
  -> {b:Bool | Prop b <=> IsGoodIndex input target i} @-}
isGoodIndex input target i 
  =  subString input i (stringLen target)  == target  
  && i + stringLen target <= stringLen input
  && 0 <= i    
