{-@ distributeInput
     :: f:(RString -> Monoid a)
     -> thm:(x1:RString -> x2:RString -> {f (x1 <+> x2) ==  (f x1) <> (f x2)} )
     -> is:RString
     -> n:Int 
     -> {f is == mconcat (map f (chunkString n is))}
     / [stringLen is] 
  @-}

distributeInput :: forall (a :: Symbol). (KnownSymbol a) 
  => (RString -> Monoid a)
  -> (RString -> RString -> Proof)
  -> RString -> Int -> Proof

distributeInput f thm is n  
  | stringLen is <= n || n <= 1
  =   mconcat (map f (chunkString n is))
  ==. mconcat (map f (C is N))
  ==. mconcat (f is `C` map f N)
  ==. (f is) <> (mconcat N)
  ==. (f is) <> (mempty :: Monoid a)
  ==. f is ? mempty_left (f is)
  *** QED 
distributeInput f thm is n  
  =   mconcat (map f (chunkString n is))
  ==. mconcat (map f (C takeIs (chunkString n dropIs))) 
  ==. mconcat (f takeIs `C` map f (chunkString n dropIs))
  ==. f takeIs <> f dropIs
       ? distributeInput f thm dropIs n  
  ==. f (takeIs <+> dropIs)
       ? thm takeIs dropIs
  ==. f is 
       ? concatTakeDrop n is 
  *** QED  
  where
    dropIs = dropString n is 
    takeIs = takeString n is 