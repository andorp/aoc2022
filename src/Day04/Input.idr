module Day04.Input

import Data.List1
import Data.String

export
partial
read1 : String -> List ((Int,Int),(Int,Int))
read1 = map parse . lines
  where
    partial
    getSections : List Int -> ((Int,Int),(Int,Int))
    getSections [a,b,c,d] = ((a,b),(c,d))

    partial
    parse : String -> ((Int,Int),(Int,Int))
    parse = getSections . toList . map (cast . fastPack) . split (not . isDigit) . fastUnpack