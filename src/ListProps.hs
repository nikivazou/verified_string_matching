{-# LANGUAGE CPP                 #-}

{-@ LIQUID "--higherorder"         @-}
{-@ LIQUID "--totality"            @-}
{-@ LIQUID "--exactdc"             @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module ListProps where

import Language.Haskell.Liquid.ProofCombinators 
import Prelude hiding (take, drop, map)

#include "AutoProofs/ListMonoidLemmata.hs"
-- #include "Proofs/ListMonoidLemmata.hs"
#include "Data/List/RList.hs"

