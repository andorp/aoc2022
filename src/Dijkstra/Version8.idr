module Dijkstra.Version8

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

record Search n start where
  constructor SearchData
  paths : SortedDMap (Vertex n) (\v => DPair Distance (\d => Path d start v))
  queue : Queue n

inQueue :
  {u : Vertex n}     ->
  Search n s         ->
  List (Neighbour u) ->
  ---------------------
  List (Neighbour u)    -- TODO: Proof that neighbours are in the queue.
inQueue d ns =
  filter (\x => elem (x.vertex) d.queue) ns

updatePath :
  (s : Search n t)   ->
  {u : Vertex n}     ->
  {du : Distance}    ->
  (dp : Path du t u) ->
  Neighbour u        -> -- TODO: This neighbour can not be the 'u' ?
  ---------------------
      (Search n t)
updatePath (SearchData paths queue) {u} {du} upath (MkNeighbour d v) = 
  SearchData
    { paths =
        case lookupPrecise v paths of
          -- v is something new, and it should be a path from u
          Nothing => insert v ((du + d) ** Step upath (Edge u)) paths
          -- we investigated v earlier and already found a path of some cost
          -- if the new cost is cheaper we have to update the path
          Just (dv ** dpath) => case (du + d < dv) of
            True  => insert v ((du + d) ** Step upath (Edge u)) paths
            False => paths
    , queue
    }

regAlts :
   (s : Search n t)   ->
   {u : Vertex n}     ->
   {d : Distance}     ->
   (p : Path d t u)   ->
   List (Neighbour u) ->
  ----------------------
      (Search n t)
regAlts s p []        = s
regAlts s p (n :: ns) = regAlts (updatePath s p n) p ns

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

distanceFun : {t : _} -> (s : Search n t) -> (Vertex n) -> Maybe Distance
distanceFun (SearchData paths queue) v = distancePathFun paths v

record FindMinResult (s : Search n t) where
  constructor MkFindMinResult
  minVertex           : Vertex n
  newSearch           : Search n t
  0 queueKeepElements : Permutation s.queue (minVertex :: newSearch.queue)
  0 minVertexProof    : All (\q => LT (distanceFun s minVertex) (distanceFun s q)) newSearch.queue

-- -- Remove the coord from the queue that has the shorted distance.
-- -- NOTE: Linear search of all the vertices in the queue.
findMinDistAndRemove :
  (d : Search n s)   ->
  (NonEmpty d.queue) ->
  ---------------------
     FindMinResult d
findMinDistAndRemove (SearchData p (c0 :: cs0)) IsNonEmpty =
  let (v ** ((rs ** (MkErased per, MkErased ds2))))
        = go c0 (map DPair.fst (lookupPrecise c0 p)) Refl cs0 [] 
                (rewrite (appendNilRightNeutral (c0 :: cs0)) in Refl)
                []
  in (MkFindMinResult v (SearchData p rs) per ds2)
  where
    data Erased : Type -> Type where MkErased : (0 x : t) -> Erased t

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
  {n : Nat}          ->
  {ok : IsSucc n}    ->
  (start : Vertex n) ->
  ---------------------
    (Search n start)
init {n=S m} {ok=ItIsSucc} start
  = SearchData  (singleton start (0 ** Node)) (forget (allFins m))

namespace FindMinPathProof

  ||| The updatePath does not change the queue in the search description.
  updatePathQueue :
    (s : Search n t)                   ->
    {u : Vertex n}                     ->
    {d : Distance}                     ->
    (p : Path du t u)                  ->
    (n : Neighbour u)                  ->
    -------------------------------------
    (updatePath s p n).queue === s.queue
  updatePathQueue (SearchData paths queue) p (MkNeighbour d v)
    = Refl

  ||| The reagAlts does not change the queue in the search description.
  export
  regAltsQueue :
    (s  : Search n t)               ->
    {u  : Vertex n}                 ->
    {d  : Distance}                 ->
    (p  : Path d t u)               ->
    (ys : List (Neighbour u))       ->
    ----------------------------------
    (regAlts s p ys).queue === s.queue
  regAltsQueue s p [] = Refl
  regAltsQueue s {d} p (n :: ns) = Calc $
    |~ (regAlts (updatePath s p n) p ns).queue
    ~~ (updatePath s p n).queue
        ... (regAltsQueue (updatePath s p n) p ns)
    ~~ s.queue
        ... (updatePathQueue s {d} p n)

Neighbours : Nat -> Type
Neighbours n = (v : Vertex n) -> List (Neighbour v)

export
findMinPath :
  {n   : Nat}                  ->
  {t   : Vertex n}             ->
  (g   : Neighbours n)         ->
  (s   : Search n t)           ->
  (c   : Nat)                  ->
  (cOk : length s.queue === c) =>
  -------------------------------
  (Paths t)
findMinPath {t} g s0 c {cOk} with (s0.queue) proof p1
  _ | [] = s0.paths
  _ | (q :: qs) = 
    let (S k) = c in
    let fm = findMinDistAndRemove s0 (rewrite p1 in IsNonEmpty) in
    let fmLength = inj S $ Calc $
    --  ^^^^^^^^ This is for termination checking
          |~ S (length ((fm.newSearch).queue))
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
    case (lookupPrecise fm.minVertex s0.paths) of
      Nothing => findMinPath g fm.newSearch k
--    ^^^^^^^ Min vertex has no path from the start yet, which also means
--    infite distance from the start, any non-processed neighbours of such
--    node means infinite plus some distance, which is still infinite,
--    and it shouldn't be registered as a valid path from the start, it must
--    be simply skipped.
      Just (du ** upath) =>
--         ^^^^^^^^^^^^^ Min vertex has a found path with the cost of du.
--    for all the non-processed neighbours of the min-vertex it must
--    be checked if the path to the neighbour is longer and if it is,
--    then its path must be updated.
        let ns = inQueue fm.newSearch (g fm.minVertex) in
        let okLength = inj S $ Calc $
              |~ S (length ((regAlts (fm.newSearch) upath ns).queue))
              ~~ S (length fm.newSearch.queue)
                ... (cong (S . length) (regAltsQueue fm.newSearch upath ns))
              ~~ S k
                ... (cong S fmLength) in
        (findMinPath g (regAlts fm.newSearch upath ns) k)
