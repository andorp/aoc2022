module Day05.Input

import Data.String

export
partial
read1 : String -> List (Nat,Nat,Nat)
read1 = map coords . lines
  where
    partial
    coords : String -> (Nat,Nat,Nat)
    coords str = case words str of
      ["move",a,"from",b,"to",c] => (cast a,cast b,cast c)
