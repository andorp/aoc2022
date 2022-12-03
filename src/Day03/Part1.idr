module Day03.Part1

import Partial
import Day03.Domain
import Data.SortedSet
import Data.Vect
import Data.List


partial
findError : Rucksack -> ValidItem
findError sack
  = unsafeHead
  $ SortedSet.toList
  $ SortedSet.intersection
      (SortedSet.fromList (toList sack.compartment1))
      (SortedSet.fromList (toList sack.compartment2))

export
partial
sumPriorities : List Rucksack -> Int
sumPriorities = foldl (\s , r => s + (priority (findError r))) 0
