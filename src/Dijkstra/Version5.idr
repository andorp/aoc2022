module Dijkstra.Version5

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

permutationLemma1 : {v:a} -> {rs : List a} -> (vs : List a) -> Permutation (v :: (vs ++ rs)) (vs ++ (v :: rs))
permutationLemma1 [] = Refl
permutationLemma1 (x :: xs) = CalcWith {leq=Permutation} $ 
  |~ (v :: (x :: (xs ++ rs)))
  <~ (x :: (v :: (xs ++ rs))) ... (Swap Refl)
  <~ (x :: (xs ++ (v :: rs))) ... (Prep (permutationLemma1 _))

permutationLemma2 : {c,v:a} -> {vs,rs : List a} -> Permutation (c :: (v :: (vs ++ rs))) (c :: (vs ++ (v :: rs)))
permutationLemma2 = CalcWith {leq=Permutation} $
  |~ (c :: (v :: (vs ++ rs)))
  <~ (c :: (vs ++ (v :: rs))) ... (Prep (permutationLemma1 _))

permutationLemma3 : {c,v:a} -> {vs,rs : List a} -> Permutation (c :: (v :: (vs ++ rs))) (v :: (vs ++ (c :: rs)))
permutationLemma3 = CalcWith {leq=Permutation} $
  |~ (c :: (v :: (vs ++ rs)))
  <~ (v :: (c :: (vs ++ rs))) ... (Swap Refl)
  <~ (v :: (vs ++ (c :: rs))) ... (Prep (permutationLemma1 _))

permutationKeepsLength : Permutation as bs -> (length as === length bs)
permutationKeepsLength Refl = Refl
permutationKeepsLength (Prep x) = cong S (permutationKeepsLength x)
permutationKeepsLength (Swap x) = cong (S . S) (permutationKeepsLength x)
permutationKeepsLength (Trans {ys} x y) = Calc $
  |~ length as
  ~~ length ys ... (permutationKeepsLength x)
  ~~ length bs ... (permutationKeepsLength y)


Vertex : (n : Nat) -> Type
Vertex n = Fin n

Distance : Type
Distance = Nat

Queue : (n : Nat) -> Type
Queue n = List (Vertex n)

data Neighbour : Vertex n -> Type where
  MkNeighbour : {u : Vertex n} -> (d : Distance) -> (v : Vertex n) -> Neighbour u

(.vertex) : {0 u : Vertex n} -> (Neighbour u) -> Vertex n
(.vertex) (MkNeighbour d v) = v

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

record ContextInvariant (s,q : Search n) where
  constructor CInvariant
  neighbourInv : s.neighbours === q.neighbours
  startInv     : s.start      === q.start

invariantContext :
  {s,q : Search n}                     ->
  (ng : s.neighbours === q.neighbours) =>
  (st : s.start === q.start)           =>
  ---------------------------------------
           ContextInvariant s q
invariantContext {ng} {st} = CInvariant ng st

Transitive (Search n) ContextInvariant where
  transitive s1 s2 = CInvariant
    { neighbourInv = transitive s1.neighbourInv s2.neighbourInv
    , startInv     = transitive s1.startInv s2.startInv
    }

record QueueInvariant (s,q : Search n) where
  constructor QInvariant
  qContextInv  : ContextInvariant s q
  queueInv     : s.queue === q.queue

invaraintQueue :
  {s,q : Search n}            ->
  (ci : ContextInvariant s q) =>
  (qu : s.queue === q.queue)  =>
  ------------------------------
        QueueInvariant s q
invaraintQueue {ci} {qu} = QInvariant ci qu

Transitive (Search n) QueueInvariant where
  transitive s1 s2 = QInvariant
    { qContextInv = transitive s1.qContextInv s2.qContextInv
    , queueInv    = transitive s1.queueInv s2.queueInv
    }

record PathsInvariant (s,q : Search n) where
  constructor PInvariant
  pContextInv : ContextInvariant s q
  pathsInv    : s.paths ~=~ q.paths

invariantPaths :
  {s,q : Search n}            ->
  (ci : ContextInvariant s q) =>
  (ps : s.paths ~=~ q.paths)  =>
  ------------------------------
        PathsInvariant s q
invariantPaths {ci} {ps} = PInvariant ci ps

inQueue :
  {u : Vertex n}     ->
  Search n           ->
  List (Neighbour u) ->
  ---------------------
  List (Neighbour u)
inQueue d ns = filter (\x => elem (x.vertex) d.queue) ns

updatePath :
             (s : Search n)         ->
             (u : Vertex n)         ->
             Neighbour u            ->
  ------------------------------------
  (z : Search n ** QueueInvariant s z)
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
    ** invaraintQueue
  )

regAlts :
             (u : Vertex n)         ->
             Maybe Distance         ->
             (s : Search n)         ->
             List (Neighbour u)     ->
  ------------------------------------
  (q : Search n ** QueueInvariant s q)
regAlts u Nothing   s0 ns = (s0 ** invaraintQueue)
regAlts u (Just du) s0 [] = (s0 ** invaraintQueue)
regAlts u (Just du) s0 (n :: ns) =
  let (s1 ** ok1) = updatePath s0 u n in
  let (s2 ** ok2) = regAlts u (Just du) s1 ns in
  (s2 ** transitive ok1 ok2)

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
  minVertex         : Vertex n
  newSearch         : Search n
  sameContext       : PathsInvariant s newSearch
  0 queueKeepElements : Permutation s.queue (minVertex :: newSearch.queue)
  0 minVertexProof    : All (\q => LT (distanceFun s minVertex) (distanceFun s q)) newSearch.queue

data Erased : Type -> Type where
  MkErased : (0 x : t) -> Erased t

-- -- Remove the coord from the queue that has the shorted distance.
-- -- NOTE: Linear search of all the vertices in the queue.
findMinDistAndRemove :
  (d : Search n)     ->
  (NonEmpty d.queue) ->
  ---------------------
     FindMinResult d
findMinDistAndRemove (SearchData neighbours start paths (c0 :: cs0)) IsNonEmpty =
  let (v ** ((rs ** (MkErased per, MkErased ds2))))
        = go c0 (map DPair.fst (lookupPrecise c0 paths)) Refl cs0 [] 
                (rewrite (appendNilRightNeutral (c0 :: cs0)) in Refl)
                []
  in (MkFindMinResult v (SearchData neighbours start paths rs) invariantPaths per ds2)
  where
    go
      :  (  c   : Vertex n) -> (d : Maybe Distance)
      -> (0 hd  : map DPair.fst (lookupPrecise c paths) === d)
      -> (  cs  : List (Vertex n))
      -> (  rs  : List (Vertex n)) 
      -> (0 per : Permutation (c0 :: cs0) (c :: cs ++ rs))
      -> (0 sml : All (\r => LT (distancePathFun paths c) (distancePathFun paths r)) rs)
      -> (v : Vertex n **
            (res : (List (Vertex n)) ** 
              ( Erased (Permutation (c0 :: cs0) (v :: res))
              , Erased (All (\r => LT (distancePathFun paths v) (distancePathFun paths r)) res)
              )))
    go c d dOk [] rs per allOk = (c ** ((rs ** (MkErased per, MkErased allOk))))
    go c d dOk (v :: vs) rs per rsOk with (map DPair.fst (lookupPrecise v paths)) proof p1
      -- Inifity distance, not candidate, keep the candidate
      _ | Nothing with (d) proof p2
        _ | Nothing  = go c d (transitive dOk (sym p2)) vs (v :: rs)
                          (transitive per permutationLemma2)
                          (infinities :: rsOk)
        _ | Just vd' = go c d (transitive dOk (sym p2)) vs (v :: rs)
                          (transitive per permutationLemma2)
                          (lessThanInfinity :: rsOk)
      _ | Just vd with (d) proof p2
        -- x distance is smaller than infinity, replace candidate with x
        _ | Nothing = go v (Just vd) p1 vs (c :: rs)
                         (transitive per permutationLemma3)
                         (lessThanInfinity :: mapProperty (Transitive lessThanInfinity) rsOk)
        _ | Just vd' with (vd < vd') proof p3
          -- x distance is smaller than infinity, replace candidate with x
          _ | True = go v (Just vd) p1 vs (c :: rs)
                        (transitive per permutationLemma3)
                        (lessThan :: mapProperty (Transitive lessThan) rsOk)
          -- c distance is smaller, keep the candidate
          _ | False = go c d (transitive dOk (sym p2)) vs (v :: rs)
                         (transitive per permutationLemma2)
                         (notLessThan2nd :: rsOk)

init :
  {n : Nat}                                           ->
  {ok : IsSucc n}                                     ->
  (neighbours : (u : Vertex n) -> List (Neighbour u)) ->
  (start : Vertex n)                                  ->
  ------------------------------------------------------
                      (Search n)
init {n=S m} {ok=ItIsSucc} neighbours start
  = SearchData neighbours start (singleton start (0 ** Node)) (forget (allFins m))

total
findMinPath :
  {n   : Nat}                  ->
  (s   : Search n)             ->
  (c   : Nat)                  ->
  (cOk : length s.queue === c) =>
  -------------------------------
  (Paths s.start)
findMinPath s0 c {cOk} with (s0.queue) proof p
  _ | [] = s0.paths
  _ | (q :: qs) with (c)
    _ | (S k) =
      let (MkFindMinResult u s1 ok1 per minPrf) = (findMinDistAndRemove s0 (rewrite p in IsNonEmpty)) in
      let ns = inQueue s1 (s1.neighbours u) in
      let (s2 ** ok2) = regAlts u (map fst (lookupPrecise u s0.paths)) s1 ns in
      let okLength = inj S $ Calc $
            |~ S (length s2.queue)
            ~~ S (length s1.queue)    ... (cong (S . length) (sym (ok2.queueInv)))
            ~~ length (u :: s1.queue) ... (Refl)
            ~~ length s0.queue        ... (sym (permutationKeepsLength per))
            ~~ length (q :: qs)       ... (cong length p)
            ~~ S (length qs)          ... (Refl)
            ~~ S k                    ... (cOk) in
      rewrite (trans ok1.pContextInv.startInv ok2.qContextInv.startInv) in (findMinPath s2 k)
