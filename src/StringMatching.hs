{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ImpredicativeTypes  #-}
{-# LANGUAGE TypeSynonymInstances #-}

{-@ LIQUID "--higherorder"         @-}
{-@ LIQUID "--totality"            @-}
{-@ LIQUID "--exactdc"             @-}
{-@ LIQUID "--no-measure-fields"   @-}
{-@ LIQUID "--trust-internals"     @-}
{-@ infix <+> @-}
{-@ infix <>  @-}

module StringMatching where

#define CheckAll
#define ParallelEvaluation


import Prelude hiding ( mempty, mappend, id, mconcat, map, (<>), Monoid 
                      , take, drop  
                      , error
                      )


import System.Environment   
import System.Exit
import Data.String hiding (fromString)
import GHC.TypeLits
import Data.Maybe 
import GHC.Generics

import Data.RString.RString
import Language.Haskell.Liquid.ProofCombinators 

import Data.Proxy 
import Control.Parallel.Strategies 


import Text.Printf
import Control.Exception
import System.CPUTime
#define MainCall


#ifdef CheckAll

#define CheckMonoidEmptyLeft
#define CheckMonoidEmptyRight
#define CheckMonoidAssoc
#define CheckDistributeInput
#define CheckParEquivalence

#include "Proofs/CastLemmata.hs"
#include "Proofs/EmptyLemmata.hs"
#include "Proofs/ListLemmata.hs"
#include "Proofs/ListMonoidLemmata.hs"
#include "Proofs/ShiftingLemmata.hs"
#include "Proofs/DistributeInput.hs"
#include "Proofs/DistributeToSM.hs"

#endif


#include "Data/List/RList.hs"
#include "Data/StringMatching/StringMatching.hs"
#include "Data/Monoid/PMonoid.hs"
#include "Data/RString/Chunk.hs"



-------------------------------------------------------------------------------
------------ | String Matching Main Theorem  ----------------------------------
-------------------------------------------------------------------------------

{-@ correctness :: SM target -> is:RString  -> n:Int -> m:Int
   -> {toSM is == toSMPar m n is } @-}

correctness :: forall (target :: Symbol). (KnownSymbol target) => SM target -> RString -> Int -> Int -> Proof
correctness _ is n m  
  =   toSMPar m n is 
  ==. (pmconcat m (map toSM (chunkString n is)) :: SM target)
  ==. mconcat (map toSM (chunkString n is))
       ? pmconcatEquivalence m (map toSM (chunkString n is) :: List (SM target))
  ==. toSM is 
       ? distributionEq (mempty :: SM target) is n 
  *** QED 


-------------------------------------------------------------------------------
------------ | Interface ------------------------------------------------------
-------------------------------------------------------------------------------


{-@ runMatching :: Pos -> Pos -> RString -> String -> IO () @-}
runMatching :: Int -> Int -> RString -> String -> IO ()
runMatching parfactor chunksize input tg =
  case someSymbolVal tg of 
    SomeSymbol (_ :: Proxy target) -> do            
      let isPar  = indicesSM (toSMPar parfactor chunksize input :: SM target)
      putStrLn   $ "Indices: " ++ show isPar
      exitSuccess 

{-@ timeSeqStringMatching :: String -> String -> IO (Int, Double) @-}
timeSeqStringMatching :: String -> String -> IO (Int, Double) 
timeSeqStringMatching input tg = 
  case someSymbolVal tg of 
    SomeSymbol (_ :: Proxy target) -> do
      let is = indicesSM (toSM (fromString input) :: SM target)
      (sec, indices) <- time (is `seq` return is)
      return (llen indices, sec)



{-@ timeParStringMatching :: Pos -> Pos -> String -> String -> IO (Int, Double) @-}
timeParStringMatching :: Int -> Int -> String -> String -> IO (Int, Double) 
timeParStringMatching parfactor chunksize input tg = 
  case someSymbolVal tg of 
    SomeSymbol (_ :: Proxy target) -> do
      let is = indicesSM (toSMPar parfactor chunksize (fromString input) :: SM target)
      (sec, indices) <- time (is `seq` return is)
      return (llen indices, sec)

time :: IO t -> IO (Double, t)
time a = do
    start <- getCPUTime
    v <- a
    end   <- getCPUTime
    let diff = (fromIntegral (end - start)) / (10^12)
    return (diff :: Double, v)

test = indicesSM (toSM (fromString $ clone 100 "ababcabcab")  :: SM "abcab" )
  where
    clone i xs = concat (replicate i xs) 

test1 = indicesSM (toSM (fromString "ababcabcab")  :: SM "abcab" )


{-@ reflect toSMPar @-}
toSMPar :: forall (target :: Symbol). (KnownSymbol target) => Int -> Int -> RString -> SM target  
toSMPar parfactor chunksize input 
--   = pmconcat parfactor (map toSM (chunkString chunksize input))
   = pmconcat parfactor (withStrategy parStrategy (map toSM (chunkString chunksize input)))




-------------------------------------------------------------------------------
----------  Proof that toSM distributes ---------------------------------------
-------------------------------------------------------------------------------
#include "Proofs/DistributeInputSM.hs"


-------------------------------------------------------------------------------
----------  Parallelization: pmconcat i is == mconcat is ----------------------
-------------------------------------------------------------------------------
#include "Proofs/PmconcatEquivalence.hs"


-------------------------------------------------------------------------------
----------  Proof that SM is a Monoid -----------------------------------------
-------------------------------------------------------------------------------

#include "Proofs/MonoidEmptyLeft.hs"
#include "Proofs/MonoidEmptyRight.hs"
#include "Proofs/MonoidAssoc.hs"
