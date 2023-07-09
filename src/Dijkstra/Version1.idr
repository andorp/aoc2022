module Dijkstra.Version1

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
  neighbours : Vertex n -> List (Distance, Vertex n)
  dist       : SortedMap (Vertex n) Distance   -- Missing entry means infinity
  prev       : SortedMap (Vertex n) (Vertex n) -- Missing entry means not connected in the path
  queue      : Queue n

inQueue : Search n -> List (Distance, Vertex n) -> List (Distance, Vertex n)
inQueue d ns = filter (\x => elem (snd x) d.queue) ns
-- inQueue d ns = filter (\(d,x) => elem x d.queue) ns
--                                         ^^^^^^^
-- While processing right hand side of inQueue. When unifying:
--     Nat
-- and:
--     Search ?n
-- Mismatch between: Nat and Search ?n.

-- Remove the coord from the queue that has the shorted distance.
-- TODO: Add invariant: The findMinDistAndRemove returns a queue which is a permutation of the selected coord and the original list.
-- NOTE: Linear search of all the vertices in the queue.
findMinDistAndRemove
  :  (d : Search n)
  -> (NonEmpty d.queue)
  -> (Search n, Vertex n)
findMinDistAndRemove (SearchData elev dist prev (c :: cs)) IsNonEmpty =
  let (q', c') = go c (lookup c dist) [] cs
  in (SearchData elev dist prev q', c')
  where
    go : Vertex n -> Maybe Distance -> List (Vertex n) -> List (Vertex n) -> (List (Vertex n), Vertex n)
    go c dc rs [] = (rs, c)
    go c dc rs (v :: vs) = case lookup v dist of
      -- Inifity distance, not candidate, keep the candidate
      Nothing => go c dc (v :: rs) vs
      Just dv => case dc of
        -- x distance is smaller than infinity, replace candidate with x
        Nothing => go v (Just dv) (c :: rs) vs
        Just dc' => if dv < dc'
          -- x distance is smaller than infinity, replace candidate with x
          then go v (Just dv) (c :: rs) vs
          -- c distance is smaller, keep the candidate
          else go c dc (v :: rs) vs

regAlts : (u : Vertex n) -> Maybe Distance -> (s : Search n) -> List (Distance, Vertex n) -> (Search n)
regAlts u du d []        = d
regAlts u du d ((e,v) :: vs) = case (du, lookup v d.dist) of
  (Nothing, _) => regAlts u du d vs
  (Just dd, Nothing) =>
    let alt = dd + e in -- The cost for any existing neighbour is one.
    regAlts u du ({ dist $= insert v alt , prev $= insert v u } d) vs -- Syntax error if ';' is used, pointing to somewhere else
  (Just dd, Just dv) =>
    let alt = dd + e in
    regAlts u du (if (alt < dv) then ({ dist $= insert v alt , prev $= insert v u } d) else d) vs

partial
findMinPath
  :  {n : Nat}
  -> (d : Search n)
  -> (s : Nat)
  -> (SortedMap (Vertex n) Distance, SortedMap (Vertex n) (Vertex n))
findMinPath d0 s with (d0.queue) proof p
  _ | [] with (s)
    _ | Z = (d0.dist, d0.prev)
  _ | (q :: qs) with (s)
    _ | (S k) =
      let (d1, u) = (findMinDistAndRemove d0 (rewrite p in IsNonEmpty)) in
      let ns = inQueue d1 (d1.neighbours u) in
      let d2 = regAlts u (lookup u d0.dist) d1 ns in
      findMinPath d2 k
