module Day09.Part1

import Data.SortedMap
import Day09.Domain
import Day09.Visualisation


namespace Visualisation

  export
  RopeVis : Type
  RopeVis = Rope -> String

  export
  render : RopeVis -> Rope -> String
  render f r = f r 

  export
  drawRope : (Int,Int) -> (Int,Int) -> RopeVis
  drawRope r c rope = drawMatrix drawChar r c
    where
      drawChar : Pos -> Maybe Char
      drawChar pos =
        if pos == rope.head
          then Just 'H'
          else if pos == rope.tail
            then Just 'T'
            else Nothing

travel
  :  {auto ref : VisitedRef}
  -> {auto vis : RopeVis}
  -> Rope -> List (Direction,Int)
  -> IO ()
travel {vis} r [] = do
  printLn r
  putStrLn $ render vis r
  visit r.tail
travel r ((d,0)::ds) = do
  travel r ds
travel r ((d,n)::ds) = do
  printLn r
  putStrLn $ render vis r
  visit r.tail
  travel (moveRope d r) ((d,n-1) :: ds)

export
part1 : List (Direction, Int) -> IO Nat
part1 directions = do
  ref <- newVisitedRef
  let vis = drawRope (-4,0) (0,5)
  travel start directions
  visited <- getVisited
  pure $ length $ SortedMap.toList visited
