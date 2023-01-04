module Day09.Visualisation

import Day09.Domain
import Data.String
import Data.SortedMap
import Data.Fin

export
drawMatrix : (Pos -> Maybe Char) -> (Int,Int) -> (Int,Int) -> String
drawMatrix getChar (rs,re) (cs,ce)
  = unlines
  $ [ fastPack
        [ fromMaybe '.' $ getChar (r,c)
        | c <- [cs .. ce]
        ]
    | r <- [rs .. re]
    ]
