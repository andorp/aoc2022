module Day08.Input

import Data.String
import Data.Vect
import Day08.Domain
import Partial

checkNonZero : (n : Nat) -> Maybe (IsSucc n)
checkNonZero 0     = Nothing
checkNonZero (S k) = Just ItIsSucc

export
partial
read : String -> Grid
read str = Partial.fromJust $ do
  let ls = lines str
  let n : Nat = length ls
  succ <- checkNonZero n
  rows <- traverse (toVect n . map (\c => ord c - 48) . fastUnpack) ls
  forest <- toVect n rows
  Just $ MkGrid n succ forest
