module Main where

import System.Process
import System.Exit
import Text.Printf

import Data.List (sort)

import StringMatching (timeParStringMatching, timeSeqStringMatching)
import Data.Foldable (foldlM)

main :: IO ()
main = do 
  -- putStrLn "\nTest Runtime..."
  -- testRunTime ()
  putStrLn "\nRun Liquid... "
  cd <- timeLiquid ()
  putStrLn "\nDone Testing"
  exitWith cd 

-- To compute time, run the proccess itenumber times and take mean
-- This does not work.... after first iteration the result is cached
itenumber = 1

-- Chunks Should be around the number of proccessors
chunks  = [2, 4, 6, 8, 10, 20, 30, 40, 60, 80, 100, 150, 200]


-- PFactor should be more than the chunk size 
pfactor = [2, 4, 6, 8, 10, 20, 30, 40, 60, 80, 100, 150, 200]

testRunTime :: () -> IO ()
testRunTime _ = do
  -- target is the string "the"
  testRunTimeOnTarget "src/tests/the_out.csv" (TString "the")
  -- target is the first 200 characters of the file 
  testRunTimeOnTarget "src/tests/big_out.csv" (TLen 400)


testRunTimeOnTarget :: String -> Target -> IO ()
testRunTimeOnTarget fn target = do 
  writeInit fn tabsep 
     ["Parfactor", "Chunks Number", "Time (sec)\t", "Speedup\t\t" ,"Input Size", "Target Size", "Indices Found"]
  t <- doSeqStringMatch fn Nothing target
  ts <- mapM (\(pf, csz) -> doParStringMatch fn (fst t) pf csz  Nothing target) 
             [ (i, j) | i <- pfactor, j <- chunks ]
  printSummary 5 (fst t) (t:ts)
  putStrLn "\n\n"

printSummary :: Int -> Double -> [(Double, (Integer, Integer))] -> IO ()
printSummary cut tseq ts = do  
  let sortedts = take cut (sort ts)
  putStrLn $ "\nBest " ++ show cut ++ " speedups:"
  putStrLn $ sep "\t|\t" ["Speedup\t", "Time (s)", "Pfact", "Chunks Number"]
  putStrLn (showTimes tseq sortedts)



showTimes ti xs = sep "\n" (map (\(t, (p, s)) -> 
  ( showSpeedup ti t ++ "\t|\t" ++ showDouble t ++ "\t|\t" ++ show p ++ "\t|\t" ++ show s )) xs)

showDouble :: Double -> String 
showDouble t 
  = (printf "%0.9f" (t :: Double) :: String)

showSpeedup :: Double -> Double -> String 
showSpeedup tseq tpar 
  = mspace ++ (printf "%0.2f %% " ((((tseq - tpar)/tseq) * 100) :: Double)  :: String) 
  where
    mspace = if tseq >= tpar then " " else ""

doSeqStringMatch :: String -> Maybe Int -> Target -> IO (Double, (Integer, Integer))
doSeqStringMatch fn insize tg = do 
  input     <- makeInput insize <$> readFile "src/tests/wilde-picture.txt"
  let target = makeTarget input tg 
  (is, sec) <- computeTime itenumber (timeSeqStringMatching input target)
  write fn doubletabsep 
    [show 1, show 1, 
     showDouble sec,
     showSpeedup sec sec,
     show $ length input, show $ length target, show $ is]
  return (sec, (1, 1))

doParStringMatch :: String -> Double -> Integer -> Integer -> Maybe Int -> Target -> IO (Double, (Integer, Integer))

doParStringMatch fn seqspeed parfactor chunksize insize tg = do 
  input     <- makeInput insize <$> readFile "src/tests/wilde-picture.txt"
  let target = makeTarget input tg 
  (is, sec) <- computeTime itenumber (timeParStringMatching parfactor (toInteger (length input `div` fromIntegral chunksize)) input target)
  write fn doubletabsep 
    [show parfactor, show chunksize, 
     showDouble sec, showSpeedup seqspeed sec,
     show $ length input, show $ length target, show $ is]
  return (sec, (parfactor, chunksize))



computeTime :: Integer -> IO (a, Double) -> IO (a, Double)
computeTime i act = go (fromIntegral i) undefined 0 
  where
    go 0 x acc = return (x, acc / (fromIntegral i ::Double))
    go i _ acc = do {(x, t) <- act; go (i-1) x (acc +t)}

writeInit fn fm xs = do
  putStrLn (fm xs)
  writeFile fn (csvfm xs ++ "\n")


write fn fm xs = do
  putStrLn (fm xs)
  appendFile fn (csvfm xs ++ "\n")


makeInput Nothing x  = x 
makeInput (Just i) x = take i x 

data Target = TString String | TLen Int 

makeTarget _ (TString t)  = t 
makeTarget input (TLen i) = take i input 

csvfm = sep ","
tabsep = sep "\t|\t"
doubletabsep = sep "\t\t|\t"

sep _ [] = []
sep _ [x] = x 
sep s (x:xs) = x ++ s ++ sep s xs 


liquidFiles :: [String]
liquidFiles 
  = [ "ListMonoidLemmata.hs"
    , "PmconcatEquivalence.hs"
    , "MonoidEmptyLeft.hs"       
    , "MonoidEmptyRight.hs"      
    , "MonoidEmptyAssoc.hs"      
    , "DistributeToSM.hs"       
    ]


runLiquidProof :: ExitCode -> String -> IO ExitCode

runLiquidProof i fm
  = do -- TOO SLOW pf <- runCommand' ("cd src; time stack exec -- liquid AutoProofs/" ++ fm ++ "> log 2>&1 ; cd ..")
       af <- runCommand' ("cd src; time stack exec -- liquid Proofs/" ++ fm ++ "> log 2>&1 ; cd ..") 
       return $ mconcat [i, af]
{-   
  = do pf <- runCommand ("stack exec -- liquid Proofs/"     ++ fm) >>= waitForProcess
       ap <- runCommand ("stack exec -- liquid AutoProofs/" ++ fm) >>= waitForProcess
       return $ mconcat [i, pf, ap] 
-}

runCommand' :: String -> IO ExitCode
runCommand' str = 
  do ps <- runCommand str -- (str ++ "> log 2>&1")
     ec <- waitForProcess ps 
     putStrLn ("\nCommand `" ++ str ++ "` exited with " ++ show ec)
     return ec


timeLiquid :: ()   -> IO ExitCode
timeLiquid _ = do 
  e1 <- runCommand' "stack install liquidhaskell" 
--   e2 <- foldlM runLiquidProof e1 liquidFiles
  e2 <- runLiquidProof mempty "PmconcatEquivalence" --  runCommand' "time stack exec -- liquid src/StringMatching.hs "  
  e3 <- runCommand' "time stack exec -- liquid src/StringMatching.hs "  
  e4 <- runCommand' "time stack exec -- liquid src/AutoStringMatching.hs "  
  return $ mconcat [e1, e2, e3, e4]

runLiquid :: ()   -> IO ExitCode
runLiquid _ = do 
  e1 <- runCommand' "stack install liquidhaskell" 
  e2 <- foldlM runLiquidProof e1 liquidFiles
  e3 <- runCommand' "time stack exec -- liquid src/StringMatching.hs "  
  e4 <- return mempty --   runCommand' "stack exec -- liquid src/AutoStringMatching.hs --debug" 
  return $ mconcat [e1, e2, e3, e4]


instance Monoid ExitCode where
  mempty = ExitSuccess
  mappend (ExitFailure i) _ = ExitFailure i 
  mappend _ (ExitFailure i) = ExitFailure i 
  mappend _ _ = ExitSuccess  

