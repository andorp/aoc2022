module Day03.Part2

import Partial
import Day03.Domain
import Data.Vect
import Data.SortedSet

-- Split to list of RuckSacks by three
-- Check the set for the rucksack for common item, there must be one
-- summarize the priorities of the 3 items

itemSet : Rucksack -> SortedSet Item
itemSet sack =
  SortedSet.union
    (SortedSet.fromList (toList sack.compartment1))
    (SortedSet.fromList (toList sack.compartment2))

partial
checkLength3 : List a -> Vect 3 a
checkLength3 = fromJust . toVect 3

export
partial
groupPriorities : List (List Rucksack) -> Int
groupPriorities = foldl addPriority 0 . map checkLength3
  where
    partial
    calcCommonItemPrio : Vect 3 Rucksack -> Int
    calcCommonItemPrio [x,y,z]
      = priority
      $ unsafeHead
      $ SortedSet.toList
      $ SortedSet.intersection
          (SortedSet.intersection (itemSet x) (itemSet y))
          (itemSet z)

    partial
    addPriority : Int -> Vect 3 Rucksack -> Int
    addPriority s xs = s + calcCommonItemPrio xs
