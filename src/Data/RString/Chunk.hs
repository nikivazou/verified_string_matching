-------------------------------------------------------------------------------
----------  String Chunking ---------------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect chunkString @-}
{-@ chunkString :: Int -> xs:RString -> List RString / [stringLen xs] @-}
chunkString :: Int -> RString -> List (RString)
chunkString i xs 
  | i <= 1 || stringLen xs <= i 
  = C xs N 
  | otherwise
  = C (takeString i xs) (chunkString i (dropString i xs))