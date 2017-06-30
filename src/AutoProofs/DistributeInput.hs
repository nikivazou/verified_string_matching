#define IncludeddistributeInput

{-@ automatic-instances distributeInput   @-}

{-@ distributeInput
     :: f:(RString -> Monoid a)
     -> thm:(x1:RString -> x2:RString -> {f (x1 <+> x2) ==  (f x1) <> (f x2)} )
     -> is:RString
     -> n:Integer 
     -> {f is == mconcat (map f (chunkString n is))}
     / [stringLen is] 
  @-}

distributeInput :: forall (a :: Symbol). (KnownSymbol a) 
  => (RString -> Monoid a)
  -> (RString -> RString -> Proof)
  -> RString -> Integer -> Proof

distributeInput f thm is n  
  | stringLen is <= n ||  n <= 1
  = mempty_left (f is)
distributeInput f thm is n  
  =   concatTakeDrop n is 
  &&& thm takeIs dropIs 
  &&& distributeInput f thm dropIs n  
  where
    dropIs = dropString n is 
    takeIs = takeString n is 