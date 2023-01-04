module Day09.Part2

import Day09.Domain
import Day09.Visualisation
import Data.SortedMap
import Data.String
import Data.List
import Data.Fin


mutual

  moveLong : Direction -> Long -> Long
  moveLong dh (End h t x) with (move dh h t x)
    _ | (dt ** x') = End (movePos dh h) (movePos dt t) x'
  moveLong dh (More h t x) with (move dh h (head t) x)
    _ | (dt ** x') = More (movePos dh h) (moveLong dt t) (rewrite (moveLongTheorem dt t) in x')

  moveLongTheorem : (d : Direction) -> (t : Long) -> head (moveLong d t) === movePos d (head t)
  moveLongTheorem d (End h t x) with (move d h t x)
    _ | (dt ** x') = Refl
  moveLongTheorem d (More h t x) with (move d h (head t) x)
    _ | (dt ** x') = Refl

namespace Visualisation

  export
  LongVis : Type
  LongVis = Long -> String

  export
  renderLong : LongVis -> Long -> String
  renderLong f l = f l

  export
  noDrawLong : LongVis
  noDrawLong = show . toList

  export
  drawLong : (Int,Int) -> (Int,Int) -> LongVis
  drawLong r c long = drawMatrix drawChar r c
    where
      longPos : List Pos
      longPos = toList long

      firstChar : String -> Char
      firstChar "0" = 'H'
      firstChar x = case strM x of
        StrNil => '?'
        StrCons x _ => x

      drawChar : Pos -> Maybe Char
      drawChar pos = map (firstChar . show) $ findIndex (==pos) longPos


travelDir
  :  {auto ref : VisitedRef}
  -> Long -> Direction -> Int -> IO Long
travelDir l d 0 = do
  visit (longTail l)
  pure l
travelDir l d n = do
  visit (longTail l)
  travelDir (moveLong d l) d (n-1)

travel
  :  {auto ref : VisitedRef}
  -> {auto vis : LongVis}
  -> Long -> List (Direction, Int)
  -> IO Long
travel {vis} l [] = do
  putStrLn $ renderLong vis l
  visit (longTail l)
  pure l
travel {vis} l ((d,n)::ds) = do
  putStrLn $ renderLong vis l
  printLn (d,n)
  l' <- travelDir l d n
  travel l' ds


export
part2 : List (Direction, Int) -> IO Nat
part2 directions = do
  ref <- newVisitedRef
  -- let vis = drawLong (-4,0) (0,5)
  -- let vis = drawLong (-15,5) (-11,14)
  let vis = noDrawLong
  _ <- travel (startLong 8) directions
  visited <- getVisited
  -- putStrLn $ drawVisited visited (-15,5) (-11,14)
  pure $ length $ SortedMap.toList visited
