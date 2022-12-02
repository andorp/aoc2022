module Day01.Input

import Data.List1
import Data.String

elves : List String -> List1 (List Int)
elves = foldl accum ([] ::: [])
  where
    accum : List1 (List Int) -> String -> List1 (List Int)
    accum (xs ::: xss) "" = [] ::: (xs :: xss)
    accum (xs ::: xss) st = (cast st :: xs) ::: xss

export
read : String -> List (List Int)
read = toList . elves . lines
