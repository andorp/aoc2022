module Dijkstra.Version6

import Data.List
import Data.List.Quantifiers
import Data.List1
import Data.Fin
import Data.Nat
import Data.SortedMap
import Data.SortedMap.Dependent
import Syntax.PreorderReasoning
import Syntax.PreorderReasoning.Generic
import Data.DPair
import Decidable.Equality
import Dijkstra.Permutation

%default total

Vertex : (n : Nat) -> Type
Vertex n = Fin n

Distance : Type
Distance = Nat

Queue : (n : Nat) -> Type
Queue n = List (Vertex n)

record Neighbour (u : Vertex n) where
  constructor MkNeighbour
  dist   : Distance
  vertex : Vertex n

data Path : (0 _ : Distance) -> (0 _ : Vertex n) -> (0 _ : Vertex n) -> Type where
  Node : Path 0 u u
  Edge : (u : Vertex x) -> Path d u v
  Step : {d,e : Nat} -> Path d u v -> Path e v w -> Path (d + e) u w

public export
Paths : {n : Nat} -> (start : Vertex n) -> Type
Paths {n} start = SortedDMap (Vertex n) (\v => DPair Distance (\d => Path d start v)) 

record Search n where
  constructor SearchData
  neighbours : (u : Vertex n) -> List (Neighbour u)
  start      : Vertex n
  paths      : SortedDMap (Vertex n) (\v => DPair Distance (\d => Path d start v))
  queue      : Queue n

inQueue :
  {u : Vertex n}     ->
  Search n           ->
  List (Neighbour u) ->
  ---------------------
  List (Neighbour u)
inQueue d ns =
  filter (\x => elem (x.vertex) d.queue) ns

updatePath :
  (s : Search n) ->
  (u : Vertex n) ->
  Neighbour u    ->
  -----------------
     (Search n)
updatePath (SearchData neighbours start paths queue) u (MkNeighbour d v) = 
  ( SearchData
      neighbours
      start
      (case lookupPrecise u paths of
        Nothing => paths -- impossible; TODO Add this fact
        Just (du ** upath) => case lookupPrecise v paths of
          -- v is something new, and it should be a path from u
          Nothing => insert v ((du + d) ** Step upath (Edge u)) paths
          -- we investigated v earlier and already found a path of some cost
          -- if the new cost is cheaper we have to update the path
          Just (dv ** dpath) => case (du + d < dv) of
            True  => insert v ((du + d) ** Step upath (Edge u)) paths
            False => paths)
      queue
  )

regAlts :
   (u : Vertex n)     ->
   Maybe Distance     ->
   (s : Search n)     ->
   List (Neighbour u) ->
  ----------------------
        (Search n)
regAlts u Nothing   s0 ns        = s0
regAlts u (Just du) s0 []        = s0
regAlts u (Just du) s0 (n :: ns) = regAlts u (Just du) (updatePath s0 u n) ns

data LT : (0 m1, m2 : Maybe Distance) -> Type where
  BothInfinity   : LT Nothing Nothing
  LessThanInf    : LT (Just x) Nothing
  LessThan1st    : (0 _ : (x < y) === True)  -> LT (Just x) (Just y)
  NotLessThan2nd : (0 _ : (y < x) === False) -> LT (Just x) (Just y)
  Transitive     : (0 _ : LT m1 m2) -> (LT m2 m3) -> LT m1 m3

infinities : (ok1 : m1 === Nothing) => (ok2 : m2 === Nothing) => LT m1 m2
infinities {ok1=Refl} {ok2=Refl} = BothInfinity

lessThanInfinity : (ok1 : m1 === Just x) => (ok2 : m2 === Nothing) => LT m1 m2
lessThanInfinity {ok1=Refl} {ok2=Refl} = LessThanInf

lessThan : (ok0 : ((x < y) === True)) => (ok1 : m1 === Just x) => (ok2 : m2 === Just y) => LT m1 m2
lessThan {ok0} {ok1=Refl} {ok2=Refl} = LessThan1st (rewrite ok0 in Refl)

notLessThan2nd : (ok0 : ((y < x) === False)) => (ok1 : m1 === Just x) => (ok2 : m2 === Just y) => LT m1 m2
notLessThan2nd {ok0} {ok1=Refl} {ok2=Refl} = NotLessThan2nd (rewrite ok0 in Refl)

distancePathFun : {s : Vertex n} -> Paths s -> (v : Vertex n) -> Maybe Distance
distancePathFun paths v = map fst (lookupPrecise v paths)

distanceFun : (s : Search n) -> (Vertex n) -> Maybe Distance
distanceFun (SearchData neighbours start paths queue) v = distancePathFun paths v

record FindMinResult (s : Search n) where
  constructor MkFindMinResult
  minVertex           : Vertex n
  newSearch           : Search n
  0 queueKeepElements : Permutation s.queue (minVertex :: newSearch.queue)
  0 minVertexProof    : All (\q => LT (distanceFun s minVertex) (distanceFun s q)) newSearch.queue

-- -- Remove the coord from the queue that has the shorted distance.
-- -- NOTE: Linear search of all the vertices in the queue.
findMinDistAndRemove :
  (d : Search n)     ->
  (NonEmpty d.queue) ->
  ---------------------
     FindMinResult d
findMinDistAndRemove (SearchData neighbours start p (c0 :: cs0)) IsNonEmpty =
  let res = go c0 (map DPair.fst (lookupPrecise c0 p)) Refl cs0 [] 
               (rewrite (appendNilRightNeutral (c0 :: cs0)) in Refl)
               []
  in (MkFindMinResult
        (fst res)
        (SearchData neighbours start p (fst (snd res)))
        (getErased (fst (snd (snd res))))
        (getErased (snd (snd (snd res)))))
  where
    data Erased : Type -> Type where MkErased : (0 x : t) -> Erased t

    0
    getErased : Erased t -> t
    getErased (MkErased x) = x

    go :
      (  c   : Vertex n) -> (d : Maybe Distance)                                   ->
      (0 hd  : map DPair.fst (lookupPrecise c p) === d)                            ->
      (  cs  : List (Vertex n))                                                    ->
      (  rs  : List (Vertex n))                                                    ->
      (0 per : Permutation (c0 :: cs0) (c :: cs ++ rs))                            ->
      (0 sml : All (\r => LT (distancePathFun p c) (distancePathFun p r)) rs)      ->
      -------------------------------------------------------------------------------
      (v : Vertex n **
          (res : (List (Vertex n)) ** 
            ( Erased (Permutation (c0 :: cs0) (v :: res))
            , Erased (All (\r => LT (distancePathFun p v) (distancePathFun p r)) res)
            )))
    go c d dOk [] rs per allOk = (c ** ((rs ** (MkErased per, MkErased allOk))))
    go c d dOk (v :: vs) rs per rsOk with (map DPair.fst (lookupPrecise v p)) proof p1
      _ | Nothing with (d) proof p2
        _ | Nothing  = go c d (transitive dOk (sym p2)) vs (v :: rs)
                          (transitive per secondMovesInside)
                          (infinities :: rsOk)
        _ | Just vd' = go c d (transitive dOk (sym p2)) vs (v :: rs)
                          (transitive per secondMovesInside)
                          (lessThanInfinity :: rsOk)
      _ | Just vd with (d) proof p2
        _ | Nothing = go v (Just vd) p1 vs (c :: rs)
                         (transitive per firstMovesNonEmptyInside)
                         (lessThanInfinity :: mapProperty (Transitive lessThanInfinity) rsOk)
        _ | Just vd' with (vd < vd') proof p3
          _ | True = go v (Just vd) p1 vs (c :: rs)
                        (transitive per firstMovesNonEmptyInside)
                        (lessThan :: mapProperty (Transitive lessThan) rsOk)
          _ | False = go c d (transitive dOk (sym p2)) vs (v :: rs)
                         (transitive per secondMovesInside)
                         (notLessThan2nd :: rsOk)

export
init :
  {n : Nat}                                           ->
  {ok : IsSucc n}                                     ->
  (neighbours : (u : Vertex n) -> List (Neighbour u)) ->
  (start : Vertex n)                                  ->
  ------------------------------------------------------
                      (Search n)
init {n=S m} {ok=ItIsSucc} neighbours start
  = SearchData neighbours start (singleton start (0 ** Node)) (forget (allFins m))

namespace FindMinPathProof

  ||| The updatePath does not change the start in the search description.
  updatePathStart :
    (s : Search n)                    ->
    (u : Vertex n)                    ->
    (x : Neighbour u)                 ->
    ------------------------------------
    (updatePath s u x).start === s.start
  updatePathStart (SearchData neighbours start paths queue) u (MkNeighbour d v)
    = Refl

  ||| The updatePath does not change the queue in the search description.
  updatePathQueue :
    (s : Search n)                     ->
    (u : Vertex n)                     ->
    (x : Neighbour u)                  ->
    -------------------------------------
    (updatePath s u x).queue === s.queue
  updatePathQueue (SearchData neighbours start paths queue) u (MkNeighbour d v)
    = Refl

  ||| The regAlts does not change the start in the search description.
  export
  regAltStart :
    (s  : Search n)                    ->
    (u  : Vertex n)                    ->
    (x  : Maybe Distance)              ->
    (ys : List (Neighbour u))          ->
    -------------------------------------
    (regAlts u x s ys).start === s.start
  regAltStart s u Nothing  [] = Refl
  regAltStart s u (Just x) [] = Refl
  regAltStart s u Nothing (n :: ns) = Refl
  regAltStart s u (Just x) (n :: ns) = Calc $
    |~ (regAlts u (Just x) (updatePath s u n) ns).start
    ~~ (updatePath s u n).start ... (regAltStart (updatePath s u n) u (Just x) ns)
    ~~ s.start                   ... (updatePathStart s u n)

  ||| The reagAlts does not change the queue in the search description.
  export
  regAltsQueue :
    (s  : Search n)                    ->
    (u  : Vertex n)                    ->
    (x  : Maybe Distance)              ->
    (ys : List (Neighbour u))          ->
    -------------------------------------
    (regAlts u x s ys).queue === s.queue
  regAltsQueue s u Nothing [] = Refl
  regAltsQueue s u Nothing (n :: ns) = Refl
  regAltsQueue s u (Just x) [] = Refl
  regAltsQueue s u (Just x) (n :: ns) = Calc $
    |~ (regAlts u (Just x) (updatePath s u n) ns).queue
    ~~ (updatePath s u n).queue ... (regAltsQueue (updatePath s u n) u (Just x) ns)
    ~~ s.queue                  ... (updatePathQueue s u n)

  export
  findMinDistAndRemoveStart :
    (s  : Search n)                                      ->
    (ne : NonEmpty s.queue)                              ->
    -------------------------------------------------------
    (findMinDistAndRemove s ne).newSearch.start === s.start
  findMinDistAndRemoveStart (SearchData neighbours start paths (c :: cs)) IsNonEmpty
    = Refl

export
findMinPath :
  {n   : Nat}                  ->
  (s   : Search n)             ->
  (c   : Nat)                  ->
  (cOk : length s.queue === c) =>
  -------------------------------
  (Paths s.start)
findMinPath s0 c {cOk} with (s0.queue) proof p1
  _ | [] = s0.paths
  _ | (q :: qs) with (c)
    _ | (S k) with (findMinDistAndRemove s0 (rewrite p1 in IsNonEmpty)) proof p2
      _ | fm =
        let ns = inQueue fm.newSearch (fm.newSearch.neighbours fm.minVertex) in
        let du = map fst (lookupPrecise fm.minVertex s0.paths) in
        let okLength = inj S $ Calc $
              |~ S (length (regAlts fm.minVertex du fm.newSearch ns).queue)
              ~~ S (length fm.newSearch.queue)
                ... (cong (S . List.length) (regAltsQueue fm.newSearch fm.minVertex du ns))
              ~~ length (fm.minVertex :: fm.newSearch.queue)
                ... (Refl)
              ~~ length s0.queue
                ... (sym (permutationKeepsLength fm.queueKeepElements))
              ~~ length (q :: qs)
                ... (cong length p1)
              ~~ S (length qs)
                ... (Refl)
              ~~ S k
                ... (cOk) in
        let okStart = Calc $
              |~ (regAlts fm.minVertex du fm.newSearch ns).start
              ~~ fm.newSearch.start
                ... (regAltStart fm.newSearch fm.minVertex du ns)
              ~~ (findMinDistAndRemove s0 (rewrite p1 in IsNonEmpty)).newSearch.start
                ... (cong (\x => x.newSearch.start) (sym p2))
              ~~ s0.start
                ... (findMinDistAndRemoveStart s0 (rewrite p1 in IsNonEmpty)) in
        rewrite (sym okStart) in (findMinPath (regAlts fm.minVertex du fm.newSearch ns) k)
