module Day05.Problem

import Data.Vect
import Data.Nat
import Data.Fin
import Day05.Domain

{-
[J]             [F] [M]             7 
[Z] [F]     [G] [Q] [F]             6
[G] [P]     [H] [Z] [S] [Q]         5
[V] [W] [Z] [P] [D] [G] [P]         4
[T] [D] [S] [Z] [N] [W] [B] [N]     3
[D] [M] [R] [J] [J] [P] [V] [P] [J] 2
[B] [R] [C] [T] [C] [V] [C] [B] [P] 1
[N] [S] [V] [R] [T] [N] [G] [Z] [W] 0
 1   2   3   4   5   6   7   8   9 
-}

export
myShip : Ship 9
myShip = MkShip
  [ mkStack "NBDTVGZJ"
  , mkStack "SRMDWPF"
  , mkStack "VCRSZ"
  , mkStack "RTJZPHG"
  , mkStack "TCJNDZQF"
  , mkStack "NVPWGSFM"
  , mkStack "GCVBPQ"
  , mkStack "ZBPN"
  , mkStack "WPJ"
  ]
