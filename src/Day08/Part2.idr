module Day08.Part2

import Data.Vect
import Data.So
import Data.DPair
import Data.Fin
import Day08.Domain


data Scenic : Int -> List Int -> Int -> Type where
  Empty : Scenic h [] 0
  Block : {h : Int} -> (t : Int) -> So      (t >= h)  -> Scenic h ts s -> Scenic h (t :: ts) 1
  More  : {h : Int} -> (t : Int) -> So (not (t >= h)) -> Scenic h ts s -> Scenic h (t :: ts) (1 + s)

scenic : (h : Int) -> (ts : List Int) -> Subset Int (Scenic h ts)
scenic h [] = Element 0 Empty
scenic h (x :: xs) with (scenic h xs) | (choose (x >= h))
  _ | Element _ prf | Left   oh = Element 1       (Block x  oh prf)
  _ | Element s prf | Right noh = Element (1 + s) (More  x noh prf)

scenicScore : Coord n -> Forest n -> Int
scenicScore x@(r,c) forest =
  let rx = row r forest
      cx = col c forest
      h     = heightAt x forest
      left  = reverse $ before c rx
      right =           after  c rx
      up    = reverse $ before r cx
      down  =           after  r cx
  in product'
      [ fst $ scenic h left
      , fst $ scenic h right
      , fst $ scenic h up
      , fst $ scenic h down
      ]
  where
    product' : List Int -> Int
    product' = product

maximum : List Int -> Int
maximum [] = 0
maximum (x :: xs) = foldr max x xs

export
part2 : Grid -> Int
part2 (MkGrid (S n) ItIsSucc forest) = maximum $ map (\c => scenicScore c forest) coords
