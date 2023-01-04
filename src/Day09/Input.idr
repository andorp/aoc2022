module Day09.Input

import Day09.Domain
import Data.String

export
partial
read : String -> List (Direction, Int)
read = map (parseDirection . fastUnpack) . lines
  where
    parseDirection : List Char -> (Direction,Int)
    parseDirection ('L'::' '::rest) = (Left , cast (fastPack rest))
    parseDirection ('R'::' '::rest) = (Right, cast (fastPack rest))
    parseDirection ('U'::' '::rest) = (Up   , cast (fastPack rest))
    parseDirection ('D'::' '::rest) = (Down , cast (fastPack rest))
