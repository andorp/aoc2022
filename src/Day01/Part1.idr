module Day01.Part1

import Data.DPair

public export
Snacks : Type
Snacks = List Int

carries : Snacks -> Int
carries = sum

public export
Calories : Type
Calories = List Snacks

greater : Int -> Int -> Int
greater x y = if x > y then x else y

data Most : Int -> (0 _ : Calories) -> Type where
  Nil  : Most 0 []
  Cons : (e : Snacks) -> Most n es -> Most (greater (carries e) n) (e :: es)

most : (c : Calories) -> (Subset Int (\m => Most m c))
most [] = Element 0 []
most (x :: xs) with (most xs)
  _ | Element m ms = Element (greater (carries x) m) (Cons x ms)

export
mostCalories : Calories -> Int
mostCalories cs with (most cs)
  _ | Element m _ = m
