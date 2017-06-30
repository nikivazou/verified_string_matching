module Main where

import StringMatching

import System.Environment   
import System.Exit
import Data.RString.RString

main :: IO ()
main = 
  do args      <- getArgs
     case args of 
       (i:j:fname:target:_) -> do input <- fromString <$> readFile fname
                                  let parfactor = (read i :: Integer ) 
                                  let chunksize = (read j :: Integer) 
                                  if parfactor <= 0  || chunksize <= 0
                                    then putStrLn "Chunksize and Parallel Factor should be positive numbers" >> return ()
                                    else runMatching parfactor chunksize input target
       _                    -> putStrLn $ "Wrong input: You need to provide the chunksize," ++
                                          "the input filename and the target string. For example:\n\n\n" ++ 
                                          "verified-string-indexing 1000 1000 input.txt abcab\n\n"
     
