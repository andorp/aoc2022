module Day03.Domain

import IsTrue
import Data.Vect
import Data.DPair

-- Solution:
-- Read file, line by line, create a Rucksack of it.
-- Read the rucksack to two sets, get the intersection of the set.

public export
Item : Type
Item = Char

||| Make sure that any complicated computation is erased.
data Erase : Type -> Type where
  MkErase : (0 _ : t) -> Erase t

export
data ValidItemIdx : Item -> Type where
  MkValidItem : {i : Item} -> Either (Erase (IsTrue (isUpper i))) (Erase (IsTrue (isLower i))) -> ValidItemIdx i

export
ValidItem : Type
ValidItem = Exists ValidItemIdx

export
Eq ValidItem where
  (Evidence _ (MkValidItem {i=a} _)) == (Evidence _ (MkValidItem {i=b} _)) = a == b

export
Ord ValidItem where
  compare (Evidence _ (MkValidItem {i=a} _)) (Evidence _ (MkValidItem {i=b} _)) = compare a b

export
mkValidItem : Item -> Maybe ValidItem
mkValidItem c with (isUpper c) proof pu
  _ | True = Just (Evidence c (MkValidItem (Left (MkErase (isTrueR pu)))))
  _ | False with (isLower c) proof pl
    _ | True = Just (Evidence c (MkValidItem (Right (MkErase (isTrueR pl)))))
    _ | False = Nothing

getItem : ValidItem -> Item
getItem (Evidence i (MkValidItem {i} _)) = i

public export
record Rucksack where
  constructor MkRucksack
  size         : Nat
  compartment1 : Vect size ValidItem
  compartment2 : Vect size ValidItem

export
Show Rucksack where
  show (MkRucksack _ comp1 comp2) = fastPack (map getItem (toList comp1) ++ map getItem (toList comp2))

export
priority : ValidItem -> Int
priority (Evidence c (MkValidItem (Left isUpper)))  = ord c - 65 + 27
priority (Evidence c (MkValidItem (Right isLower))) = ord c - 97 + 1

example1 : IO ()
example1 = do
  printLn (map priority (mkValidItem 'a'), 1)
  printLn (map priority (mkValidItem 'z'), 26)
  printLn (map priority (mkValidItem 'A'), 27)
  printLn (map priority (mkValidItem 'Z'), 53)
