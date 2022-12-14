module Day01.Part2

import Data.So
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

||| The relation between the Top3 Calories.
|||
||| It must built up from the relations how the swap of numbers can be built up, and only
||| we can have a valid start.
|||
||| To build this releation we will have to implement some algorithm, which must respect
||| this sketch.
data Top3Prm : (Int,Int,Int) -> Type where
  Start : All So [x >= y, y >= z] -> Top3Prm (x,y,z)
  Fst   : So (n > x) -> Top3Prm (x,y,z) -> Top3Prm (n,x,y)
  Snd   : So (n > y) -> Top3Prm (x,y,z) -> Top3Prm (x,n,y)
  Thd   : So (n > z) -> Top3Prm (x,y,z) -> Top3Prm (x,y,n)

||| We are really interested in the Int triplet.
|||
||| The associated proof with it should be thrown away.
Top3 : Type
Top3 = Subset (Int,Int,Int) Top3Prm

||| Little helper to create the Top3 value.
start : (x,y,z : Int) -> {auto prf : All So [x >= y, y >= z]} -> Top3
start x y z {prf} = Element (x,y,z) (Start prf)

||| Implementation of the Top3 relation respecting swap algorithm.
top3 : Int -> Top3 -> Top3
top3 n (Element (g1,g2,g3) w) with (n > g1) proof ng1
  _ | True  = Element (n,g1,g2) (Fst (eqToSo ng1) w)
  _ | False with (n > g2) proof ng2
    _ | True  = Element (g1,n,g2) (Snd (eqToSo ng2) w)
    _ | False with (n > g3) proof ng3
      _ | True = Element (g1,g2,n) (Thd (eqToSo ng3) w)
      _ | False = Element (g1,g2,g3) w

||| The relation that describes how to find the top 3 calories.
data Top3Search : Top3 -> (0 _ : Calories) -> Type where
  Nil  : Top3Search (start 0 0 0) []
  Cons : (x : Snacks) -> (0 _ : Top3Search n xs) -> Top3Search (top3 (carries x) n) (x :: xs)

top3Search : (c : Calories) -> (Subset Top3 (\g => Top3Search g c))
top3Search [] = Element (start 0 0 0) []
top3Search (x :: xs) with (top3Search xs)
  _ | Element m ms = Element (top3 (carries x) m) (Cons x ms)

export
top3Calories : Calories -> Int
top3Calories cs with (top3Search cs)
  _ | Element (Element (x,y,z) _) _ = x + y + z
