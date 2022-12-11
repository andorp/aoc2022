module Day06.Input

import Data.Vect
import Data.List

export
testInput : String
testInput = "mjqjpqmgbljsphdztnvjfqwrcgsmlb"
-- testInput = "bvwbjplbgvbhsrlpgdmjqwftvncz"
-- testInput = "nppdvjthqldpwncqszvftbrmjlhg"
-- testInput = "nznrnfrfntjfmvfwmzdfjlvtqnbhcprsg"
-- testInput = "zcfzfwzzqfrljwzlrfnpqdbhtmscgvjw"

readChars : (n : Nat) -> IsSucc n -> List Char -> List (Vect n Char)
readChars _     _        []        = []
readChars (S n) ItIsSucc (c :: cs) = case toVect (S n) (take (S n) (c :: cs)) of
  Nothing => []
  Just xs => xs :: (readChars (S n) ItIsSucc cs)

readBlocks : List Char -> List (Vect 4 Char)
readBlocks = readChars 4 ItIsSucc

readMessages : List Char -> List (Vect 14 Char)
readMessages = readChars 14 ItIsSucc

export
read1 : String -> List (Vect 4 Char)
read1 xs = readBlocks $ fastUnpack xs

export
read2 : String -> List (Vect 14 Char)
read2 xs = readMessages $ fastUnpack xs
