module Dijkstra.Version3

import Data.List
import Data.List1
import Data.Fin
import Data.Nat
import Data.SortedMap
import Syntax.PreorderReasoning
import Syntax.PreorderReasoning.Generic
import Data.DPair


Vertex : (n : Nat) -> Type
Vertex n = Fin n

Distance : Type
Distance = Nat

Queue : (n : Nat) -> Type
Queue n = List (Vertex n)

record Search n where
  constructor SearchData
  neighbours : (u : Vertex n) -> List (Distance, Vertex n)
  dist       : SortedMap (Vertex n) Distance   -- Missing entry means infinity
  prev       : SortedMap (Vertex n) (Vertex n) -- Missing entry means not connected in the path
  queue      : Queue n

inQueue : Search n -> List (Distance, Vertex n) -> List (Distance, Vertex n)
inQueue d ns = filter (\x => elem (snd x) d.queue) ns

namespace List

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

0
permutationLemma1 : (vs : List a) -> Permutation (v :: (vs ++ rs)) (vs ++ (v :: rs))
permutationLemma1 [] = Refl
permutationLemma1 (x :: xs) = CalcWith {leq=Permutation} $ 
  |~ (v :: (x :: (xs ++ rs)))
  <~ (x :: (v :: (xs ++ rs))) ... (Swap Refl)
  <~ (x :: (xs ++ (v :: rs))) ... (Prep (permutationLemma1 _))

0
permutationLemma2 : Permutation (c :: (v :: (vs ++ rs))) (c :: (vs ++ (v :: rs)))
permutationLemma2 = CalcWith {leq=Permutation} $
  |~ (c :: (v :: (vs ++ rs)))
  <~ (c :: (vs ++ (v :: rs))) ... (Prep (permutationLemma1 _))

0
permutationLemma3 : Permutation (c :: (v :: (vs ++ rs))) (v :: (vs ++ (c :: rs)))
permutationLemma3 = CalcWith {leq=Permutation} $
  |~ (c :: (v :: (vs ++ rs)))
  <~ (v :: (c :: (vs ++ rs))) ... (Swap Refl)
  <~ (v :: (vs ++ (c :: rs))) ... (Prep (permutationLemma1 _))

0
permutationKeepsLength : Permutation as bs -> (length as === length bs)
permutationKeepsLength Refl = Refl
permutationKeepsLength (Prep x) = cong S (permutationKeepsLength x)
permutationKeepsLength (Swap x) = cong (S . S) (permutationKeepsLength x)
permutationKeepsLength (Trans {ys} x y) = Calc $
  |~ length as
  ~~ length ys ... (permutationKeepsLength x)
  ~~ length bs ... (permutationKeepsLength y)

-- Remove the coord from the queue that has the shorted distance.
-- NOTE: Linear search of all the vertices in the queue.
findMinDistAndRemove
  :  (d : Search n)
  -> (NonEmpty d.queue)
  -> (v : Vertex n ** (Subset (Search n) (\q => Permutation d.queue (v :: q.queue))))
findMinDistAndRemove (SearchData elev dist prev (c0 :: cs0)) IsNonEmpty =
  let (v ** (Element rs per)) = go c0 (lookup c0 dist) cs0 [] (rewrite (appendNilRightNeutral (c0 :: cs0)) in Refl)
  in (v ** (Element (SearchData elev dist prev rs) per))
  where
    go
      :  (  c   : Vertex n) -> Maybe Distance
      -> (  cs  : List (Vertex n))
      -> (  rs  : List (Vertex n)) 
      -> (0 per : Permutation (c0 :: cs0) (c :: cs ++ rs))
      -> (v : Vertex n ** (Subset (List (Vertex n)) (\res => Permutation (c0 :: cs0) (v :: res))))
    go c d [] rs per = (c ** (Element rs per))
    go c d (v :: vs) rs per with (lookup v dist)
      -- Inifity distance, not candidate, keep the candidate
      _ | Nothing = go c d vs (v :: rs) (Trans per permutationLemma2)
      _ | Just vd with (d)
        -- x distance is smaller than infinity, replace candidate with x
        _ | Nothing = go v (Just vd) vs (c :: rs) (Trans per permutationLemma3)
        _ | Just vd' with (vd < vd')
          -- x distance is smaller than infinity, replace candidate with x
          _ | True = go v (Just vd) vs (c :: rs) (Trans per permutationLemma3)
          -- c distance is smaller, keep the candidate
          _ | False = go c d vs (v :: rs) (Trans per permutationLemma2)

updateDist : (SortedMap (Vertex n) Distance -> SortedMap (Vertex n) Distance) -> (Search n) -> (Search n)
updateDist u s = { dist $= u } s

0
updateDistQueueLemma : (u : _) -> (s : _) -> s.queue === (updateDist u s).queue
updateDistQueueLemma u (SearchData neighbours dist prev queue) = Refl

updatePrev : (SortedMap (Vertex n) (Vertex n) -> SortedMap (Vertex n) (Vertex n)) -> (Search n) -> (Search n)
updatePrev u s = { prev $= u } s

0
updatePrevQueueLemma : (u : _) -> (s : _) -> s.queue === (updatePrev u s).queue
updatePrevQueueLemma u (SearchData neighbours dist prev queue) = Refl

regAlts : (u : Vertex n) -> Maybe Distance -> (s : Search n) -> List (Distance, Vertex n) -> (q : Search n ** s.queue === q.queue)
regAlts u du d [] = (d ** Refl)
regAlts u du d ((e,v) :: vs) with (du)
  _ | Nothing = regAlts u du d vs
  _ | Just dd with (lookup v d.dist)
    _ | Nothing with (updateDist (insert v (dd + 1)) $ updatePrev (insert v u) d) proof p1
      _ | d' with (regAlts u du d' vs)
        _ | (q ** ok) =
              (q ** Calc $
                |~ d.queue
                ~~ (updatePrev (insert v u) d).queue                                  ... (updatePrevQueueLemma _ _)
                ~~ (updateDist (insert v (dd + 1)) (updatePrev (insert v u) d)).queue ... (updateDistQueueLemma _ _)
                ~~ d'.queue                                                           ... (cong (.queue) p1)
                ~~ q.queue                                                            ... (ok))
    _ | Just dv with (dd + 1 < dv)
      _ | True with (updateDist (insert v (dd + 1)) $ updatePrev (insert v u) d) proof p1
        _ | d' with (regAlts u du d' vs)
          _ | (q ** ok) =
                (q ** Calc $
                  |~ d.queue
                  ~~ (updatePrev (insert v u) d).queue                                  ... (updatePrevQueueLemma _ _)
                  ~~ (updateDist (insert v (dd + 1)) (updatePrev (insert v u) d)).queue ... (updateDistQueueLemma _ _)
                  ~~ d'.queue                                                           ... (cong (.queue) p1)
                  ~~ q.queue                                                            ... (ok))
      _ | False = regAlts u du d vs

total
findMinPath
  :  {n : Nat}
  -> (d : Search n)
  -> (s : Nat)
  -> (length d.queue === s)
  -> (SortedMap (Vertex n) Distance, SortedMap (Vertex n) (Vertex n))
findMinPath d0 s sp with (d0.queue) proof p
  _ | [] with (s)
    _ | Z = (d0.dist, d0.prev)
  _ | (q :: qs) with (s)
    _ | (S k) =
      let (u ** (Element d1 perm)) = (findMinDistAndRemove d0 (rewrite p in IsNonEmpty)) in
      let ns = inQueue d1 (d1.neighbours u) in
      let (d2 ** ok) = regAlts u (lookup u d0.dist) d1 ns in
      findMinPath d2 k $ inj S $ Calc $
        |~ S (length d2.queue)
        ~~ S (length d1.queue)    ... (cong (S . length) (sym ok))
        ~~ length (u :: d1.queue) ... (Refl)
        ~~ length d0.queue        ... (sym (permutationKeepsLength perm))
        ~~ length (q :: qs)       ... (cong length p)
        ~~ S (length qs)          ... (Refl)
        ~~ S k                    ... (sp)
