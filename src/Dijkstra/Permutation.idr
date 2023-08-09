module Dijkstra.Permutation

import Control.Relation
import Control.Order
import Syntax.PreorderReasoning
import Syntax.PreorderReasoning.Generic

public export
data Permutation : (xs, ys : List a) -> Type where
  Refl  : Permutation xs xs
  Prep  : Permutation xs ys -> Permutation (x :: xs)      (x :: ys)
  Swap  : Permutation xs ys -> Permutation (x :: y :: xs) (y :: x :: ys)
  Trans : Permutation xs ys -> Permutation ys zs -> Permutation xs zs

trans : Permutation xs ys -> Permutation ys zs -> Permutation xs zs
trans Refl q = q
trans p Refl = p
trans p q = Trans p q

-- Id function, it should be optimized away
sym : Permutation xs ys -> Permutation ys xs
sym Refl        = Refl
sym (Prep x)    = Prep (sym x)
sym (Swap x)    = Swap (sym x)
sym (Trans x y) = Trans (sym y) (sym x)

public export Reflexive   (List a) Permutation where reflexive  = Refl
public export Transitive  (List a) Permutation where transitive = trans
public export Symmetric   (List a) Permutation where symmetric  = sym
public export Equivalence (List a) Permutation where
public export Preorder    (List a) Permutation where

export
firstMovesInside : {v : a} -> {vs,rs : List a} -> Permutation (v :: (vs ++ rs)) (vs ++ (v :: rs))
firstMovesInside {vs=[]} = Refl
firstMovesInside {v} {vs=(x :: xs)} = CalcWith {leq=Permutation} $ 
  |~ (v :: (x :: (xs ++ rs)))
  <~ (x :: (v :: (xs ++ rs))) ... (Swap Refl)
  <~ (x :: (xs ++ (v :: rs))) ... (Prep firstMovesInside)

export
secondMovesInside : {c,v : a} -> {vs,rs : List a} -> Permutation (c :: (v :: (vs ++ rs))) (c :: (vs ++ (v :: rs)))
secondMovesInside = CalcWith {leq=Permutation} $
  |~ (c :: (v :: (vs ++ rs)))
  <~ (c :: (vs ++ (v :: rs))) ... (Prep firstMovesInside)

export
firstMovesNonEmptyInside : {c,v : a} -> {vs,rs : List a} -> Permutation (c :: (v :: (vs ++ rs))) (v :: (vs ++ (c :: rs)))
firstMovesNonEmptyInside {c,v,vs,rs} = firstMovesInside {v=c} {vs=v::vs} {rs=rs}

-- permutationLemma3 = CalcWith {leq=Permutation} $
--   |~ (c :: (v :: (vs ++ rs)))
--   <~ (v :: (c :: (vs ++ rs))) ... (Swap Refl)
--   <~ (v :: (vs ++ (c :: rs))) ... (Prep firstMovesInside)

export
permutationKeepsLength : Permutation as bs -> (length as === length bs)
permutationKeepsLength Refl = Refl
permutationKeepsLength (Prep x) = cong S (permutationKeepsLength x)
permutationKeepsLength (Swap x) = cong (S . S) (permutationKeepsLength x)
permutationKeepsLength (Trans {ys} x y) = Calc $
  |~ length as
  ~~ length ys ... (permutationKeepsLength x)
  ~~ length bs ... (permutationKeepsLength y)