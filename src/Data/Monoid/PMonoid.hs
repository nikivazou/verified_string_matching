{-@ withStrategy :: Strategy a -> x:a -> {v:a | v == x} @-}

parStrategy :: Strategy (List a)
#ifdef ParallelEvaluation
parStrategy = parTraversable rseq
#else 
parStrategy = r0 
#endif


{-@ axiomatize pmconcat @-}
pmconcat :: forall (a :: Symbol). (KnownSymbol a) => Int -> List (Monoid a) -> Monoid a 
{-@ pmconcat :: Int -> is:List (Monoid a) -> Monoid a /[llen is] @-}
pmconcat i xs
  | i <= 1 || llen xs <= i 
  = mconcat xs 
pmconcat i xs 
  = pmconcat i (withStrategy parStrategy (map mconcat (chunk i xs)))


mconcat  :: forall (a :: Symbol). (KnownSymbol a) => List (Monoid a) -> Monoid a 
{-@ axiomatize mconcat @-}
mconcat N        = mempty
mconcat (C x xs) =  x <> (mconcat xs)