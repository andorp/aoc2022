module Dijkstra.Version2

import Data.List
import Data.Fin
import Data.Nat
import Data.SortedMap
import Control.WellFounded
import Syntax.PreorderReasoning
import Control.Function


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

lengthAppendLemma : (xs, ys : List a) -> length (xs ++ ys) === length xs + length ys
lengthAppendLemma []        ys = Refl
lengthAppendLemma (x :: xs) ys = cong S (lengthAppendLemma xs ys)

elemInTheMiddleLemma : (y : a) -> (xs,ys : List a) -> S (length (xs ++ ys)) === length (xs ++ y :: ys)
elemInTheMiddleLemma y xs ys = Calc $
  |~ S (length (xs ++ ys))          
  ~~ S (length xs + length ys)      ... (cong S (lengthAppendLemma _ _))
  ~~ length xs + (S (length ys))    ... (plusSuccRightSucc _ _)
  ~~ length xs + (length (y :: ys)) ... (cong (length xs +) Refl)
  ~~ length (xs ++ (y :: ys))       ... (sym (lengthAppendLemma _ _))

-- Remove the coord from the queue that has the shorted distance.
-- TODO: Add invariant: The findMinDistAndRemove returns a queue which is a permutation of the selected coord and the original list.
-- NOTE: Linear search of all the vertices in the queue.
findMinDistAndRemove
  :  (d : Search n)
  -> (NonEmpty d.queue)
  -> ((q : Search n ** length d.queue === S (length q.queue)), Vertex n)
findMinDistAndRemove (SearchData elev dist prev (c :: cs)) IsNonEmpty =
  let ((q' ** q'prf), c') = go c (lookup c dist) [] cs
  in ((SearchData elev dist prev q' ** cong S (sym q'prf)), c')
  where
    go : Vertex n -> Maybe Distance -> (rs : List (Vertex n)) -> (cs : List (Vertex n)) -> ((result : (List (Vertex n)) ** length result === length (rs ++ cs)) , Vertex n)
    go c dc rs []
      =  ( (rs ** Calc $
              |~ length rs
              ~~ length (rs ++ []) ... (cong length (sym (appendNilRightNeutral _))))
         , c
         )
    go c dc rs (v :: vs) with (lookup v dist)
      -- Inifity distance, not candidate, keep the candidate
      _ | Nothing with (go c dc (v :: rs) vs)
        _ | ((res ** ok), rv) =
              ( (res ** Calc $
                  |~ length res
                  ~~ S (length (rs ++ vs))    ... (ok)
                  ~~ length (rs ++ (v :: vs)) ... (elemInTheMiddleLemma _ _ _))
              , rv
              )
      _ | Just dv with (dc)
        -- x distance is smaller than infinity, replace candidate with x
        _ | Nothing with (go v (Just dv) (c :: rs) vs)
          _ | ((res ** ok), rv) =
                ( (res ** Calc $
                    |~ length res
                    ~~ S (length (rs ++ vs))    ... (ok)
                    ~~ length (rs ++ (v :: vs)) ... (elemInTheMiddleLemma _ _ _))
                , rv
                )
        _ | Just dc' with (dv < dc')
          -- x distance is smaller than infinity, replace candidate with x
          _ | True with (go v (Just dv) (c :: rs) vs)
            _ | ((res ** ok), rv) =
                  ( (res ** Calc $
                      |~ length res
                      ~~ S (length (rs ++ vs))    ... (ok)
                      ~~ length (rs ++ (v :: vs)) ... (elemInTheMiddleLemma _ _ _))
                  , rv
                  )
          -- c distance is smaller, keep the candidate
          _ | False with (go c dc (v :: rs) vs)
            _ | ((res ** ok), rv) =
                  ( (res ** Calc $
                      |~ length res
                      ~~ S (length (rs ++ vs))    ... (ok)
                      ~~ length (rs ++ (v :: vs)) ... (elemInTheMiddleLemma _ _ _))
                  , rv
                  )

updateDist : (SortedMap (Vertex n) Distance -> SortedMap (Vertex n) Distance) -> (Search n) -> (Search n)
updateDist u s = { dist $= u } s

updateDistQueueLemma : (u : _) -> (s : _) -> s.queue === (updateDist u s).queue
updateDistQueueLemma u (SearchData neighbours dist prev queue) = Refl

updatePrev : (SortedMap (Vertex n) (Vertex n) -> SortedMap (Vertex n) (Vertex n)) -> (Search n) -> (Search n)
updatePrev u s = { prev $= u } s

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
      let ((d1 ** lprf), u) = (findMinDistAndRemove d0 (rewrite p in IsNonEmpty)) in
      let ns = inQueue d1 (d1.neighbours u) in
      let (d2 ** ok) = regAlts u (lookup u d0.dist) d1 ns in
      findMinPath d2 k $ inj S $ Calc $
        |~ S (length d2.queue)
        ~~ S (length d1.queue) ... (cong S (cong length (sym ok)))
        ~~ length d0.queue     ... (sym lprf)
        ~~ length (q :: qs)    ... (cong List.length p)
        ~~ S (length qs)       ... (Refl)
        ~~ S k                 ... (sp)
