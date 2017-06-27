{-# LANGUAGE OverloadedStrings   #-}

{-@ LIQUID "--higherorder"         @-}
{-@ LIQUID "--totality"            @-}
{-@ LIQUID "--exactdc"             @-}

module Data.RString.RString where

import qualified Data.ByteString as BS
import qualified Data.String     as ST
import Language.Haskell.Liquid.ProofCombinators 


{-@ embed Data.ByteString.Internal.ByteString as Str @-}

type RString = BS.ByteString 
--   deriving (Eq, Show)

------------------------------------------------------------------------------
---------------  RString Interface in Logic --------------------------------
------------------------------------------------------------------------------


{-@ invariant {s:RString | 0 <= stringLen s } @-}

{-@ infix <+> @-}

{-@ measure stringEmp    :: RString @-}
{-@ measure stringLen    :: RString -> Int @-}
{-@ measure subString    :: RString -> Int -> Int -> RString @-}
{-@ measure <+> :: RString -> RString -> RString @-}
{-@ measure fromString   :: String -> RString @-}
{-@ measure takeString   :: Int -> RString -> RString @-}
{-@ measure dropString   :: Int -> RString -> RString @-}



------------------------------------------------------------------------------
---------------  RString operators -----------------------------------------
------------------------------------------------------------------------------

{-@ assume (<+>) :: x:RString -> y:RString 
                 -> {v:RString | v == x <+> y && stringLen v == stringLen x + stringLen y } @-}
(<+>) :: RString -> RString -> RString
(<+>) (s1) (s2) = (s1 `BS.append` s2)

{-@ assume stringEmp :: {v:RString | v == stringEmp  && stringLen v == 0 } @-}
stringEmp :: RString
stringEmp = (BS.empty)

stringLen :: RString -> Integer   
{-@ assume stringLen :: x:RString -> {v:INat | v == stringLen x} @-}
stringLen s = toInteger (BS.length s)

{-@ assume subString  :: s:RString -> offset:Integer -> ln:Integer -> {v:RString | v == subString s offset ln } @-}
subString :: RString -> Integer -> Integer -> RString 
subString (s) o l =  (BS.take l' $ BS.drop o' s)
  where
    l' = fromInteger l 
    o' = fromInteger o  

{-@ assume takeString :: i:INat -> xs:{RString | i <= stringLen xs } -> {v:RString | stringLen v == i && v == takeString i xs } @-} 
takeString :: Integer -> RString -> RString
takeString i s = BS.take i' s
  where
    i' = fromInteger i 

{-@ assume dropString :: i:INat -> xs:{RString | i <= stringLen xs } -> {v:RString | stringLen v == stringLen xs - i && v == dropString i xs } @-} 
dropString :: Integer -> RString -> RString
dropString i s = BS.drop i' s
  where
    i' = fromInteger i 

{-@ assume fromString :: i:String -> {o:RString | i == o && o == fromString i} @-}
fromString :: String -> RString
fromString =  ST.fromString 

{-@ assume isNullString :: i:RString -> {b:Bool | Prop b <=> stringLen i == 0 } @-} 
isNullString :: RString -> Bool 
isNullString s = BS.length s == 0 


------------------------------------------------------------------------------
---------------  RStrings is Monoid ---------------------------
------------------------------------------------------------------------------

stringLeftId :: RString -> Proof
{-@ assume stringLeftId :: x:RString -> { x <+> stringEmp == x} @-}
stringLeftId _ = trivial


stringRightId :: RString -> Proof
{-@ assume stringRightId :: x:RString -> {stringEmp <+> x == x} @-}
stringRightId _ = trivial

stringAssoc :: RString -> RString -> RString -> Proof
{-@ assume stringAssoc :: x:RString -> y:RString -> z:RString 
     -> {(x <+> y) <+> z == x <+> (y <+> z) } @-}
stringAssoc _ _ _ = trivial
------------------------------------------------------------------------------
---------------  Properties assumed for RStrings ---------------------------
------------------------------------------------------------------------------

-- | Empty Strings 

{-@ assume stringEmpProp :: x:RString  -> { stringLen x == 0 <=> x == stringEmp } @-}
stringEmpProp :: RString -> Proof
stringEmpProp _ = trivial 
 

concatStringNeutralLeft :: RString -> Proof
{-@ assume concatStringNeutralLeft :: x:RString -> { x <+> stringEmp == x} @-}
concatStringNeutralLeft _ = trivial




concatStringNeutralRight :: RString -> Proof
{-@ assume concatStringNeutralRight :: x:RString -> {stringEmp <+> x == x} @-}
concatStringNeutralRight _ = trivial

{-@ concatEmpLeft :: xi:{RString | stringLen xi == 0} -> yi:RString -> { xi <+> yi == yi} @-}
concatEmpLeft :: RString -> RString -> Proof
concatEmpLeft xi yi 
  =   (xi <+> yi) 
  ==. (stringEmp <+> yi) ? stringEmpProp xi 
  ==. yi                 ? concatStringNeutralRight yi
  *** QED 


{-@ concatEmpRight :: xi:RString -> yi:{RString | stringLen yi == 0} -> { xi <+> yi == xi} @-}
concatEmpRight :: RString -> RString -> Proof
concatEmpRight xi yi 
  =   xi <+> yi 
  ==. xi <+> stringEmp ? stringEmpProp yi 
  ==. xi                        ? concatStringNeutralLeft xi 
  *** QED 

-- | Concat

{-@ assume concatTakeDrop :: i:INat -> xs:{RString | i <= stringLen xs} 
    -> {xs == (takeString i xs) <+> (dropString i xs) }  @-}
concatTakeDrop :: Integer -> RString -> Proof 
concatTakeDrop _ _ = trivial

concatLen :: RString -> RString -> Proof
{-@ assume concatLen :: x:RString -> y:RString -> { stringLen (x <+> y) == stringLen x + stringLen y } @-}
concatLen _ _ = trivial

concatStringAssoc :: RString -> RString -> RString -> Proof
{-@ assume concatStringAssoc :: x:RString -> y:RString -> z:RString 
     -> {(x <+> y) <+> z == x <+> (y <+> z) } @-}
concatStringAssoc _ _ _ = trivial


-- | Substrings 

{-@ assume subStringConcatBack :: input:RString -> input':RString -> j:Integer -> i:{Integer | i + j <= stringLen input }
  -> { (subString input i j == subString (input <+> input') i j) 
    && (stringLen input <= stringLen (input <+> input'))
     } @-}
subStringConcatBack :: RString -> RString -> Integer -> Integer -> Proof 
subStringConcatBack _ _ _ _ = trivial  


{-@ assume subStringConcatFront  
  :: input:RString -> input':RString -> j:Integer -> i:Integer 
  -> { (subString input i j == subString (input' <+> input) (stringLen input' + i) j)
      && (stringLen (input' <+> input) == stringLen input + stringLen input')
    } @-}
subStringConcatFront :: RString -> RString -> Integer -> Integer -> Proof
subStringConcatFront _ _ _ _ = trivial
