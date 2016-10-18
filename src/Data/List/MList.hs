
data Monoid (a :: Symbol) where 
  M :: Monoid a

{-@ data Monoid a = M @-}


{-@ reflect mempty @-}
{-@ reflect <> @-}
{-@ infix   <> @-}
mempty :: forall (a :: Symbol). (KnownSymbol a) => Monoid a 
mempty = M
(<>) :: forall (a :: Symbol). (KnownSymbol a) => Monoid a -> Monoid a -> Monoid a
M <> M = M 


-------------------------------------------------------------------------------
---------------------  Monoid Laws --------------------------------------------
-------------------------------------------------------------------------------

{-@ mempty_left :: x:Monoid a -> { x <> mempty == x } @-}
mempty_left :: forall (a :: Symbol). (KnownSymbol a) => Monoid a -> Proof 
mempty_left M = (M :: Monoid a) <> mempty ==. (M :: Monoid a) *** QED 

{-@ mempty_right :: x:Monoid a -> { mempty <> x == x } @-}
mempty_right :: forall (a :: Symbol). (KnownSymbol a) => Monoid a -> Proof 
mempty_right M = mempty <> (M :: Monoid a) ==. (M :: Monoid a) *** QED 

mappend_assoc :: forall (a :: Symbol). (KnownSymbol a) => Monoid a -> Monoid a -> Monoid a -> Proof 
{-@ mappend_assoc :: x:Monoid a -> y:Monoid a -> z:Monoid a -> { x <> (y <> z) = (x <> y) <> z} @-}
mappend_assoc M M M = (M :: Monoid a) <> (M <> M) ==. (M <> M) <> M *** QED 
