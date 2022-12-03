module Day03.Domain

import IsTrue
import Data.Vect
import Data.DPair

-- Solution:
-- Read file, line by line, create a Rucksack of it.
-- Read the rucksack to two sets, get the intersection of the set.

public export
RawItem : Type
RawItem = Char

export
data Item : Type where
  Upper : (i : RawItem) -> (0 _ : IsTrue (isUpper i)) -> Item
  Lower : (i : RawItem) -> (0 _ : IsTrue (isLower i)) -> Item

getRawItem : Item -> RawItem
getRawItem (Upper i x) = i
getRawItem (Lower i x) = i

export
Eq Item where
  a == b = getRawItem a == getRawItem b

export
Ord Item where
  compare a b = compare (getRawItem a) (getRawItem b)

export
mkValidItem : RawItem -> Maybe Item
mkValidItem c with (isUpper c) proof pu
  _ | True = Just (Upper c (isTrueR pu))
  _ | False with (isLower c) proof pl
    _ | True = Just (Lower c (isTrueR pl))
    _ | False = Nothing

public export
record Rucksack where
  constructor MkRucksack
  size         : Nat
  compartment1 : Vect size Item
  compartment2 : Vect size Item

export
Show Rucksack where
  show (MkRucksack _ comp1 comp2) = fastPack (map getRawItem (toList comp1) ++ map getRawItem (toList comp2))

export
priority : Item -> Int
priority (Upper i x) = ord i - 65 + 27
priority (Lower i x) = ord i - 97 + 1

example1 : IO ()
example1 = do
  printLn (map priority (mkValidItem 'a'), 1)
  printLn (map priority (mkValidItem 'z'), 26)
  printLn (map priority (mkValidItem 'A'), 27)
  printLn (map priority (mkValidItem 'Z'), 53)
