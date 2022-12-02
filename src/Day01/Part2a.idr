module Day01.Part2a

import Data.DPair
import Data.List.Quantifiers

public export
Snacks : Type
Snacks = List Int

carries : Snacks -> Int
carries = sum

public export
Calories : Type
Calories = List Snacks

Top3 : Type
Top3 = (Int,Int,Int)

greater3 : Int -> Top3 -> Top3
greater3 n (g1,g2,g3)
  = if (n > g1) then (n,g1,g2)
    else if (n > g2) then (g1,n,g2)
    else if (n > g3) then (g1,g2,n)
    else (g1,g2,g3)

sumTriple3 : Top3 -> Int
sumTriple3 (x,y,z) = x + y + z

data Most3 : Top3 -> (0 _ : Calories) -> Type where
  Nil  : Most3 (0,0,0) []
  Cons : (x : Snacks) -> Most3 n xs -> Most3 (greater3 (carries x) n) (x :: xs)

most3 : (c : Calories) -> (Subset Top3 (\m => Most3 m c))
most3 [] = Element (0, 0, 0) []
most3 (x :: xs) with (most3 xs)
 _ | Element m ms = Element (greater3 (carries x) m) (Cons x ms)

export
most3Calories : Calories -> Int
most3Calories cs with (most3 cs)
  _ | Element x _ = sumTriple3 x
