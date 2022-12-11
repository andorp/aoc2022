module Day05.Part1

import Data.Vect
import Day05.Domain
import Day05.Problem

export
code : List Move -> IO String
code moves = do
  Just result <- program9000 myShip moves
    | Nothing => pure "Nothing"
  pure $ shipMessage result
