module Day08.Part1

import Data.Vect
import Data.Fin
import Data.List1
import Day08.Domain
import Debug.Trace

visible : {n : Nat} -> Coord n -> Forest n -> Bool
visible x@(r,c) forest =
  let rx    = row r forest
      cx    = col c forest
      h     = heightAt x forest
      left  = before c rx
      right = after  c rx
      up    = before r cx
      down  = after  r cx
  in or'
      [ all (<h) left
      , all (<h) right
      , all (<h) up
      , all (<h) down
      ]
  where
    or' : List (Lazy Bool) -> Bool
    or' = or

export
part1 : Grid -> Int
part1 (MkGrid (S m) ItIsSucc forest) = sum $ map (\c => countTrue (visible c forest)) $ coords
  where
    countTrue : Bool -> Int
    countTrue True  = 1
    countTrue False = 0
