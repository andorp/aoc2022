module Day08.Domain

import Data.Vect
import Data.Fin
import Data.List
import Data.List1
import Syntax.PreorderReasoning


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

foldrImplGoLemma
  :  (x : a) -> (xs : Vect n a) -> (f : a -> b -> b) -> (e : b) -> (go : b -> b)
  -> go (foldrImpl f e (f x) xs) === foldrImpl f e (go . (f x)) xs
foldrImplGoLemma z []        f e go = Refl
foldrImplGoLemma z (y :: ys) f e go = Calc $
  |~ go (foldrImpl f e ((f z) . (f y)) ys)     
  ~~ go ((f z) (foldrImpl f e (f y) ys))       ... (cong go (sym (foldrImplGoLemma y ys f e (f z))))
  ~~ (go . (f z)) (foldrImpl f e (f y) ys)     ... (cong go Refl)
  ~~ foldrImpl f e (go . (f z) . (f y)) ys     ... (foldrImplGoLemma y ys f e (go . (f z)))

toListLemma : (x : a) -> (xs : Vect n a) -> (toList (x :: xs) === x :: toList xs)
toListLemma a []        = Refl
toListLemma a (b :: bs) = Calc $
  |~ (toList (a :: (b :: bs)))
  ~~ (foldrImpl (::) [] (\x => a :: (b :: x)) bs) ... (Refl)
  ~~ (Prelude.(::) a (foldrImpl (::) [] (\x => b :: x) bs))
      ... (sym (foldrImplGoLemma b bs (Prelude.(::)) [] (Prelude.(::) a)))
  ~~ (a :: (toList (b :: bs))) ... (Refl)

inBoundsLemma : (i : Fin n) -> (xs : Vect n a) -> InBounds (finToNat i) (toList xs)
inBoundsLemma FZ     (y :: ys) = rewrite (toListLemma y ys) in InFirst
inBoundsLemma (FS f) (y :: ys) = rewrite (toListLemma y ys) in (InLater (inBoundsLemma f ys))

indexLemma : (i : Fin n) -> (xs : Vect n a) -> (index i xs === index (finToNat i) (toList xs) {ok=inBoundsLemma i xs})
indexLemma FZ     (y :: ys) = rewrite (toListLemma y ys) in Refl
indexLemma (FS f) (y :: ys) = rewrite (toListLemma y ys) in (indexLemma f ys)

beforeLemma : (i : Fin n) -> (xs : Vect n a) -> (before i xs === take (finToNat i) (toList xs))
beforeLemma FZ     (y :: ys) = Refl
beforeLemma (FS f) (y :: ys) = rewrite (toListLemma y ys) in cong (y::) (beforeLemma f ys)

afterLemma : (i : Fin n) -> (xs : Vect n a) -> (after i xs === drop (1 + finToNat i) (toList xs))
afterLemma FZ     (y :: ys) = rewrite (toListLemma y ys) in Refl
afterLemma (FS f) (y :: ys) = rewrite (toListLemma y ys) in (afterLemma f ys)

takeIndexDropLemma : (i : Nat) -> (xs : List a) -> InBounds i xs -> (take i xs ++ [index i xs] ++ drop (1+i) xs) === xs
takeIndexDropLemma 0     (x :: xs) InFirst     = Refl
takeIndexDropLemma (S k) (x :: xs) (InLater l) = cong (x::) (takeIndexDropLemma k xs l)

beforeAfterTheorem : (i : Fin n) -> (xs : Vect n a) -> before i xs ++ [index i xs] ++ after i xs === toList xs
beforeAfterTheorem i xs = Calc $
  |~ before i xs ++ ([index i xs] ++ after i xs)
  ~~ (take (finToNat i) (toList xs)) ++ ([index i xs] ++ after i xs)
      ... (cong (++ (index i xs :: after i xs)) (beforeLemma i xs))
  ~~ (take (finToNat i) (toList xs)) ++ ([index (finToNat i) (toList xs) {ok=inBoundsLemma i xs}] ++ after i xs)
      ... (cong (\e => (take (finToNat i) (toList xs) ++ ([e] ++ after i xs))) (indexLemma i xs))
  ~~ (take (finToNat i) (toList xs)) ++ ([index (finToNat i) (toList xs) {ok=inBoundsLemma i xs}] ++ (drop (1 + finToNat i) (toList xs)))
      ... (cong (\e => (take (finToNat i) (toList xs) ++ ([index (finToNat i) (toList xs) {ok=inBoundsLemma i xs}] ++ e))) (afterLemma i xs))
  ~~ toList xs
      ... (takeIndexDropLemma (finToNat i) (toList xs) (inBoundsLemma i xs))
