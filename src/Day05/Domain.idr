module Day05.Domain

import Data.Vect
import Data.Nat
import Data.Fin
import Data.String
import Partial
-- import Data.Vect.Quantifiers

import Data.List
import Control.Monad.Identity


public export
Crate : Type
Crate = Char

public export
Stack : Type
Stack = (n : Nat ** Vect n Crate)

public export
mkStack : String -> Stack
mkStack xs = MkDPair _ (fromList (fastUnpack xs))

showStack : Stack -> String
showStack (_ ** xs) = fastPack $ toList xs

public export
data Ship : Nat -> Type where
  MkShip : {auto shipOk : IsSucc n} -> Vect n Stack -> Ship n

shipStacks : Ship n -> Vect n Stack
shipStacks (MkShip s) = s

showShip : Ship n -> String
showShip (MkShip xs) = unlines $ toList $ map showStack xs

export
shipMessage : Ship n -> String
shipMessage (MkShip css) = fastPack $ toList $ map lastChar css
  where
    lastChar : (n ** Vect n Char) -> Char
    lastChar (0     ** cs) = '?'
    lastChar ((S k) ** cs) = Vect.last cs

public export
data StackIdx : Nat -> Type where
  Idx : IsSucc n => Fin n -> StackIdx n

mkStartIdx : {n : Nat} -> IsSucc n => (x : Nat) -> Maybe (StackIdx n)
mkStartIdx 0         = Nothing
mkStartIdx {n} (S k) = do
  f <- natToFin k n
  Just $ Idx f

getIdx : StackIdx n -> Fin n
getIdx (Idx f) = f

public export
data Move : Type where
  MkMove : (from, to, many : Nat) -> Move

data CanMove : (n : Nat) -> (Ship n) -> (StackIdx n) -> (many : Nat) -> Type where
  YesCanMove
    :  (s : Ship n)
    -> (from : StackIdx n)
    -> (many : Nat)
    -> LTE many (fst (Vect.index (getIdx from) (shipStacks s)))
    -> CanMove n s from many

decCanMove : {n : Nat} -> (s : Ship n) -> (from : StackIdx n) -> (many : Nat) -> Dec (CanMove n s from many)
decCanMove s f m with (isLTE m ((fst (Vect.index (getIdx f) (shipStacks s)))))
  _ | No  contra = No (\(YesCanMove _ _ _ prf) => contra prf)
  _ | Yes prf    = Yes $ YesCanMove s f m prf

data SafeMove : (n : Nat) -> (Ship n) -> Type where
  MkSafeMove
    :  {n : Nat}
    -> (from, to : StackIdx n)
    -> (s : Ship n)
    -> (many : Nat)
    -> CanMove n s from many
    -> SafeMove n s

checkMove : {n : Nat} -> IsSucc n => (s : Ship n) -> Move -> Maybe (SafeMove n s)
checkMove s (MkMove from to many) = do
  f <- mkStartIdx from
  t <- mkStartIdx to
  let Yes prf = decCanMove s f many
      | No _ => Nothing
  Just $ MkSafeMove f t s many prf

takeEnd : {n : Nat} -> (m : Nat) -> Vect (n + m) a -> Vect m a
takeEnd {n = 0}     m xs = xs
takeEnd {n = (S k)} m (x :: xs) = takeEnd {n=k} m xs

lteSub : {m,k : Nat} -> LTE m k -> (l ** (k === l + m))
lteSub {m = 0} {k = k} LTEZero = (k ** rewrite plusZeroRightNeutral k in Refl)
lteSub {m = (S left)} {k = (S right)} (LTESucc x) with (lteSub x)
  _ | (l ** prf) = rewrite prf in (l ** rewrite plusSuccRightSucc l left in Refl)

addManyTo : {m : Nat} -> Ship n -> StackIdx n -> Vect m Crate -> Ship n
addManyTo (MkShip {shipOk} css) (Idx to) cs
  = MkShip {shipOk}
  $ Vect.updateAt to (\(m ** xs) => (_ ** (xs ++ cs)))
  $ css

recomputeLength : {k : Nat} -> (m : Nat) -> LTE m k -> Vect k a -> (l ** Vect (l + m) a)
recomputeLength {k} m prf xs with (lteSub prf)
    _ | (l ** prf2) = (l ** rewrite (sym prf2) in xs)

removeManyFrom : {n : Nat} -> (s : Ship n) -> (from : StackIdx n) -> (many : Nat) -> CanMove n s from many -> (Vect many Crate, Ship n)
removeManyFrom (MkShip {shipOk} css) from many (YesCanMove (MkShip {shipOk} css) from many lte) = -- do
  let (l ** ys) = recomputeLength many lte ((Vect.index (getIdx from) css).snd)
      css1      = Vect.replaceAt (getIdx from) (_ ** Vect.take l ys) css
      topCrates = takeEnd many ys
  in (topCrates, MkShip {shipOk} css1)

rearrange9000 : (s : Ship n) -> SafeMove n s -> Ship n
rearrange9000 s (MkSafeMove from to s many y) = 
  let (crates, css1) = removeManyFrom s from many y
  in  addManyTo css1 to (Vect.reverse crates)

export
program9000 : {n : Nat} -> IsSucc n => Ship n -> List Move -> IO (Maybe (Ship n))
program9000 s [] = do
  -- putStrLn "Ship:"
  -- putStrLn $ showShip s
  pure $ Just s
program9000 s (x :: xs) = do
  -- putStrLn "Ship:"
  -- putStrLn $ showShip s
  let Just m = checkMove s x
      | Nothing => do
          putStrLn "Invalid move."
          pure Nothing
  program9000 (rearrange9000 s m) xs

rearrange9001 : (s : Ship n) -> SafeMove n s -> Ship n
rearrange9001 s (MkSafeMove from to s many y) = 
  let (crates, css1) = removeManyFrom s from many y
  in  addManyTo css1 to crates

export
program9001 : {n : Nat} -> IsSucc n => Ship n -> List Move -> IO (Maybe (Ship n))
program9001 s [] = do
  -- putStrLn "Ship:"
  -- putStrLn $ showShip s
  pure $ Just s
program9001 s (x :: xs) = do
  -- putStrLn "Ship:"
  -- putStrLn $ showShip s
  let Just m = checkMove s x
      | Nothing => do
          putStrLn "Invalid move."
          pure Nothing
  program9001 (rearrange9001 s m) xs

namespace Example

  {-
      [D]    
  [N] [C]    
  [Z] [M] [P]
  1   2   3 
  -}    
  testShip : Ship 3
  testShip = MkShip
    [ mkStack "ZN"
    , mkStack "MCD"
    , mkStack "P"
    ]

  partial
  testProgram : List Move
  testProgram =
    [ MkMove 2 1 1
    , MkMove 1 3 3
    , MkMove 2 1 2
    , MkMove 1 2 1
    ]

  export
  partial
  examples : IO ()
  examples = do
    _ <- program9000 testShip testProgram
    pure ()
