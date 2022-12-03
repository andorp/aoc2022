module Day03.Input

import Partial
import Day03.Domain
import Data.List
import Data.Nat
import Data.Vect
import Data.String


rucksack : String -> Maybe Rucksack
rucksack line = do
  let chars = fastUnpack line
  items <- traverse mkValidItem chars
  let n0 : Nat = length items
  let n : Nat = divNatNZ n0 2 %search
  -- let n : Nat = divNatNZ n0 2 _ -- ???
  let (comp1L, comp2L) = splitAt n items
  comp1L <- toVect n comp1L
  comp2L <- toVect n comp2L
  Just $ MkRucksack n comp1L comp2L

export  
read1 : String -> List Rucksack
read1 = mapMaybe rucksack . lines


groupBy : Nat -> List a -> List (List a)
groupBy n xs = finalStep $ foldl split (n,[],[]) xs
  where
    finalStep : (Nat, List a, List (List a)) -> List (List a)
    finalStep (_, [], xss) = reverse xss
    finalStep (_, xs, xss) = reverse (reverse xs :: xss)

    split : (Nat, List a, List (List a)) -> a -> (Nat, List a, List (List a))
    split (Z  , xs, xss) a = (n, [], reverse (a :: xs) :: xss)
    split (S m, xs, xss) a = (m, a :: xs, xss)

0
groupByExample1 : groupBy 0 [] === []
groupByExample1 = Refl

0
groupByExample2 : groupBy 1 [] === []
groupByExample2 = Refl

0
groupByExample3 : groupBy 2 [1,2,3,4,5] === [[1,2,3], [4,5]]
groupByExample3 = Refl

0
groupByExample4 : groupBy 0 [1,2] === [[1], [2]]
groupByExample4 = Refl

export
partial
read2 : String -> List (List Rucksack)
read2 = groupBy 2 . map (fromJust . rucksack) . lines
