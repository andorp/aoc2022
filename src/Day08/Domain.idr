module Day08.Domain

import Data.Vect
import Data.Fin
import Data.List
import Data.List1


public export
Height : Type
Height = Int

public export
Forest : Nat -> Type
Forest n = Vect n (Vect n Height) -- Rows of columns

public export
Coord : Nat -> Type
Coord n = (Fin n, Fin n) -- Row, Column; (y,x)

export
row : Fin n -> Forest n -> Vect n Height
row r rs = index r rs

export
col : Fin n -> Forest n -> Vect n Height
col c rs = map (index c) rs 

export
heightAt : Coord n -> Forest n -> Height
heightAt (r,c) f = index c (index r f)

-- c=>
-- 30373  r
-- 25512 ||
-- 65332 \/
-- 33549
-- 35390
public export
record Grid where
  constructor MkGrid
  size     : Nat
  nonEmpty : IsSucc size
  forest   : Forest size

export
Show Grid where
  show (MkGrid size _ forest) = show forest

export
coords : {n : Nat} -> List (Coord (S n))
coords = [ (x,y) | x <- fins, y <- fins ]
  where
    fins : {n : Nat} -> List (Fin (S n))
    fins {n} = toList $ allFins n

export
before : Fin n -> Vect n a -> List a
before FZ     xs        = []
before (FS f) (x :: xs) = x :: before f xs

0 beforeEx1 : before 0 [1] === []; beforeEx1 = Refl
0 beforeEx2 : before 1 [1,2] === [1]; beforeEx2 = Refl

export
after : Fin n -> Vect n a -> List a
after FZ     xs        = drop 1 $ toList xs
after (FS f) (x :: xs) = after f xs

0 afterEx1 : after 0 [0] === []; afterEx1 = Refl
0 afterEx2 : after 1 [0,1,2,3] === [2,3]; afterEx2 = Refl

beforeAfterTheorem : (i : Fin n) -> (xs : Vect n a) -> before i xs ++ [index i xs] ++ after i xs === toList xs
beforeAfterTheorem = ?todo1
