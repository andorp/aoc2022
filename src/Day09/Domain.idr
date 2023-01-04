module Day09.Domain

import Data.SortedMap
import Data.IORef
import Data.List1
import Data.DPair


public export
Pos : Type
Pos = (Int, Int) -- Row,Col

export
data Equals : Int -> Int -> Type where
  Same  : (x : Int) -> Equals x x
  Pred  : Equals x y -> Equals (x - 1) (y - 1)
  Succ  : Equals x y -> Equals (x + 1) (y + 1)
  MPR   : Equals x ((y - 1) + 1) -> Equals x ((y + 1) - 1) 
  PMR   : Equals x ((y + 1) - 1) -> Equals x ((y - 1) + 1) 
  MPRZ  : Equals x ((y - 1) + 1) -> Equals x y           
  PMRZ  : Equals x ((y + 1) - 1) -> Equals x y           
  MPRZr : Equals x y -> Equals x ((y - 1) + 1)
  PMRZr : Equals x y -> Equals x ((y + 1) - 1)

||| The relation between head and tail, first is head, second is tail.
||| Name of constructors are for the position of the tail relative to the head.
export
data Touching : (0 _ : Pos) -> (0 _ : Pos) -> Type where
  ||| T..
  ||| .H.
  ||| ...
  TopLeft       : {0 hr,hc,tr,tc : Int} -> (0 row : Equals tr (hr - 1)) -> (0 col : Equals tc (hc - 1)) -> Touching (hr,hc) (tr,tc)
  ||| .T.
  ||| .H.
  ||| ...
  TopMiddle     : {0 hr,hc,tr,tc : Int} -> (0 row : Equals tr (hr - 1)) -> (0 col : Equals tc hc) -> Touching (hr,hc) (tr,tc)
  ||| ..T
  ||| .H.
  ||| ...
  TopRight      : {0 hr,hc,tr,tc : Int} -> (0 row : Equals tr (hr - 1)) -> (0 col : Equals tc (hc + 1)) -> Touching (hr,hc) (tr,tc)
  ||| ...
  ||| TH.
  ||| ...
  MiddleLeft    : {0 hr,hc,tr,tc : Int} -> (0 row : Equals tr hr) -> (0 col : Equals tc (hc - 1)) -> Touching (hr,hc) (tr,tc)
  ||| ...
  ||| .H.
  ||| ...
  Covers        : {0 hr,hc,tr,tc : Int} -> (0 row : Equals tr hr) -> (0 col : Equals tc hc) -> Touching (hr,hc) (tr,tc)
  ||| ...
  ||| .HT
  ||| ...
  MiddleRight   : {0 hr,hc,tr,tc : Int} -> (0 row : Equals tr hr) -> (0 col : Equals tc (hc + 1)) -> Touching (hr,hc) (tr,tc)
  ||| ...
  ||| .H.
  ||| T..
  BottomLeft    : {0 hr,hc,tr,tc : Int} -> (0 row : Equals tr (hr + 1)) -> (0 col : Equals tc (hc - 1)) -> Touching (hr,hc) (tr,tc)
  ||| ...
  ||| .H.
  ||| .T.
  BottomMiddle  : {0 hr,hc,tr,tc : Int} -> (0 row : Equals tr (hr + 1)) -> (0 col : Equals tc hc) -> Touching (hr,hc) (tr,tc)
  ||| ...
  ||| .H.
  ||| ..T
  BottomRight   : {0 hr,hc,tr,tc : Int} -> (0 row : Equals tr (hr + 1)) -> (0 col : Equals tc (hc + 1)) -> Touching (hr,hc) (tr,tc)

public export
data Direction = UpLeft | Up | UpRight | Left | Stay | Right | DownLeft | Down | DownRight

export
Show Direction where
  show UpLeft     = "UpLeft"
  show Up         = "Up"
  show UpRight    = "UpRight"
  show Left       = "Left"
  show Stay       = "Stay"
  show Right      = "Right"
  show DownLeft   = "DownLeft"
  show Down       = "Down"
  show DownRight  = "DownRight"

public export
movePos : Direction -> Pos -> Pos
movePos UpLeft    (r,c) = (r-1,c-1)
movePos Up        (r,c) = (r-1,c  )
movePos UpRight   (r,c) = (r-1,c+1)
movePos Left      (r,c) = (r  ,c-1)
movePos Stay      (r,c) = (r  ,c  )
movePos Right     (r,c) = (r  ,c+1)
movePos DownLeft  (r,c) = (r+1,c-1)
movePos Down      (r,c) = (r+1,c  )
movePos DownRight (r,c) = (r+1,c+1)

moveUpLeft : (h,t : Pos) -> Touching h t -> (dt ** Touching (movePos UpLeft h) (movePos dt t))
moveUpLeft h@(hr,hc) t@(tr,tc) (TopLeft      row col) = (Stay   ** Covers       row col)
moveUpLeft h@(hr,hc) t@(tr,tc) (TopMiddle    row col) = (Stay   ** MiddleRight  row (MPRZr col))
moveUpLeft h@(hr,hc) t@(tr,tc) (TopRight     row col) = (Left   ** MiddleRight  row (PMR (Pred col)))
moveUpLeft h@(hr,hc) t@(tr,tc) (MiddleLeft   row col) = (Stay   ** BottomMiddle (MPRZr row) col)
moveUpLeft h@(hr,hc) t@(tr,tc) (Covers       row col) = (Stay   ** BottomRight  (MPRZr row) (MPRZr col))
moveUpLeft h@(hr,hc) t@(tr,tc) (MiddleRight  row col) = (UpLeft ** MiddleRight  (Pred row) (PMR (Pred col)))
moveUpLeft h@(hr,hc) t@(tr,tc) (BottomLeft   row col) = (Up     ** BottomMiddle (PMR (Pred row)) col)
moveUpLeft h@(hr,hc) t@(tr,tc) (BottomMiddle row col) = (UpLeft ** BottomMiddle (PMR (Pred row)) (Pred col))
moveUpLeft h@(hr,hc) t@(tr,tc) (BottomRight  row col) = (UpLeft ** BottomRight  (PMR (Pred row)) (PMR (Pred col)))

moveUp : (h,t : Pos) -> Touching h t -> (dt ** Touching (movePos Up h) (movePos dt t))
moveUp h@(hr,hc) t@(tr,tc) (TopLeft      row col) = (Stay    ** MiddleLeft   row col)
moveUp h@(hr,hc) t@(tr,tc) (TopMiddle    row col) = (Stay    ** Covers       row col)
moveUp h@(hr,hc) t@(tr,tc) (TopRight     row col) = (Stay    ** MiddleRight  row col)
moveUp h@(hr,hc) t@(tr,tc) (MiddleLeft   row col) = (Stay    ** BottomLeft   (MPRZr row) col)
moveUp h@(hr,hc) t@(tr,tc) (Covers       row col) = (Stay    ** BottomMiddle (MPRZr row) col)
moveUp h@(hr,hc) t@(tr,tc) (MiddleRight  row col) = (Stay    ** BottomRight  (MPRZr row) col)
moveUp h@(hr,hc) t@(tr,tc) (BottomLeft   row col) = (UpRight ** BottomMiddle (PMR (Pred row)) (MPRZ (Succ col)))
moveUp h@(hr,hc) t@(tr,tc) (BottomMiddle row col) = (Up      ** BottomMiddle (PMR (Pred row)) col)
moveUp h@(hr,hc) t@(tr,tc) (BottomRight  row col) = (UpLeft  ** BottomMiddle (PMR (Pred row)) (PMRZ (Pred col)))

moveUpRight : (h,t : Pos) -> Touching h t -> (dt ** Touching (movePos UpRight h) (movePos dt t))
moveUpRight h@(hr,hc) t@(tr,tc) (TopLeft      row col) = (Right   ** MiddleLeft row (MPR (Succ col)))
moveUpRight h@(hr,hc) t@(tr,tc) (TopMiddle    row col) = (Stay    ** MiddleLeft row (PMRZr col))
moveUpRight h@(hr,hc) t@(tr,tc) (TopRight     row col) = (Stay    ** Covers row col)
moveUpRight h@(hr,hc) t@(tr,tc) (MiddleLeft   row col) = (UpRight ** MiddleLeft (Pred row) (MPR (Succ col)))
moveUpRight h@(hr,hc) t@(tr,tc) (Covers       row col) = (Stay    ** BottomLeft (MPRZr row) (PMRZr col))
moveUpRight h@(hr,hc) t@(tr,tc) (MiddleRight  row col) = (Stay    ** BottomMiddle (MPRZr row) col)
moveUpRight h@(hr,hc) t@(tr,tc) (BottomLeft   row col) = (UpRight ** BottomLeft (PMR (Pred row)) (MPR (Succ col)))
moveUpRight h@(hr,hc) t@(tr,tc) (BottomMiddle row col) = (UpRight ** BottomMiddle (PMR (Pred row)) (Succ col))
moveUpRight h@(hr,hc) t@(tr,tc) (BottomRight  row col) = (Up      ** BottomMiddle (PMR (Pred row)) col)

moveLeft : (h,t : Pos) -> Touching h t -> (dt ** Touching (movePos Left h) (movePos dt t))
moveLeft h@(hr,hc) t@(tr,tc) (TopLeft      row col) = (Stay      ** TopMiddle row col)
moveLeft h@(hr,hc) t@(tr,tc) (TopMiddle    row col) = (Stay      ** TopRight row (MPRZr col))
moveLeft h@(hr,hc) t@(tr,tc) (TopRight     row col) = (DownLeft  ** MiddleRight (MPRZ (Succ row)) (PMR (Pred col)))
moveLeft h@(hr,hc) t@(tr,tc) (MiddleLeft   row col) = (Stay      ** Covers row col)
moveLeft h@(hr,hc) t@(tr,tc) (Covers       row col) = (Stay      ** MiddleRight row (MPRZr col))
moveLeft h@(hr,hc) t@(tr,tc) (MiddleRight  row col) = (Left      ** MiddleRight row (PMR (Pred col)))
moveLeft h@(hr,hc) t@(tr,tc) (BottomLeft   row col) = (Stay      ** BottomMiddle row col)
moveLeft h@(hr,hc) t@(tr,tc) (BottomMiddle row col) = (Stay      ** BottomRight row (MPRZr col))
moveLeft h@(hr,hc) t@(tr,tc) (BottomRight  row col) = (UpLeft    ** MiddleRight (PMRZ (Pred row)) (PMR (Pred col)))

moveRight : (h,t : Pos) -> Touching h t -> (dt ** Touching (movePos Right h) (movePos dt t))
moveRight h@(hr,hc) t@(tr,tc) (TopLeft      row col) = (DownRight ** MiddleLeft (MPRZ (Succ row)) (MPR (Succ col)))
moveRight h@(hr,hc) t@(tr,tc) (TopMiddle    row col) = (Stay      ** TopLeft row (PMRZr col))
moveRight h@(hr,hc) t@(tr,tc) (TopRight     row col) = (Stay      ** TopMiddle row col)
moveRight h@(hr,hc) t@(tr,tc) (MiddleLeft   row col) = (Right     ** MiddleLeft row (MPR (Succ col)))
moveRight h@(hr,hc) t@(tr,tc) (Covers       row col) = (Stay      ** MiddleLeft row (PMRZr col))
moveRight h@(hr,hc) t@(tr,tc) (MiddleRight  row col) = (Stay      ** Covers row col)
moveRight h@(hr,hc) t@(tr,tc) (BottomLeft   row col) = (UpRight   ** MiddleLeft (PMRZ (Pred row)) (MPR (Succ col)))
moveRight h@(hr,hc) t@(tr,tc) (BottomMiddle row col) = (Stay      ** BottomLeft row (PMRZr col))
moveRight h@(hr,hc) t@(tr,tc) (BottomRight  row col) = (Stay      ** BottomMiddle row col)

moveDownLeft : (h,t : Pos) -> Touching h t -> (dt ** Touching (movePos DownLeft h) (movePos dt t))
moveDownLeft h@(hr,hc) t@(tr,tc) (TopLeft      row col) = (Down     ** TopMiddle (MPR (Succ row)) col)
moveDownLeft h@(hr,hc) t@(tr,tc) (TopMiddle    row col) = (DownLeft ** TopMiddle (MPR (Succ row)) (Pred col))
moveDownLeft h@(hr,hc) t@(tr,tc) (TopRight     row col) = (DownLeft ** TopRight (MPR (Succ row)) (PMR (Pred col)))
moveDownLeft h@(hr,hc) t@(tr,tc) (MiddleLeft   row col) = (Stay     ** TopMiddle (PMRZr row) col)
moveDownLeft h@(hr,hc) t@(tr,tc) (Covers       row col) = (Stay     ** TopRight (PMRZr row) (MPRZr col))
moveDownLeft h@(hr,hc) t@(tr,tc) (MiddleRight  row col) = (DownLeft ** MiddleRight (Succ row) (PMR (Pred col)))
moveDownLeft h@(hr,hc) t@(tr,tc) (BottomLeft   row col) = (Stay     ** Covers row col)
moveDownLeft h@(hr,hc) t@(tr,tc) (BottomMiddle row col) = (Stay     ** MiddleRight row (MPRZr col))
moveDownLeft h@(hr,hc) t@(tr,tc) (BottomRight  row col) = (Left     ** MiddleRight row (PMR (Pred col)))

moveDown : (h,t : Pos) -> Touching h t -> (dt ** Touching (movePos Down h) (movePos dt t))
moveDown h@(hr,hc) t@(tr,tc) (TopLeft      row col) = (DownRight ** TopMiddle (MPR (Succ row)) (MPRZ (Succ col)))
moveDown h@(hr,hc) t@(tr,tc) (TopMiddle    row col) = (Down      ** TopMiddle (MPR (Succ row)) col)
moveDown h@(hr,hc) t@(tr,tc) (TopRight     row col) = (DownLeft  ** TopMiddle (MPR (Succ row)) (PMRZ (Pred col)))
moveDown h@(hr,hc) t@(tr,tc) (MiddleLeft   row col) = (Stay      ** TopLeft (PMRZr row) col)
moveDown h@(hr,hc) t@(tr,tc) (Covers       row col) = (Stay      ** TopMiddle (PMRZr row) col)
moveDown h@(hr,hc) t@(tr,tc) (MiddleRight  row col) = (Stay      ** TopRight (PMRZr row) col)
moveDown h@(hr,hc) t@(tr,tc) (BottomLeft   row col) = (Stay      ** MiddleLeft row col)
moveDown h@(hr,hc) t@(tr,tc) (BottomMiddle row col) = (Stay      ** Covers row col)
moveDown h@(hr,hc) t@(tr,tc) (BottomRight  row col) = (Stay      ** MiddleRight row col)

moveDownRight : (h,t : Pos) -> Touching h t -> (dt ** Touching (movePos DownRight h) (movePos dt t))
moveDownRight h@(hr,hc) t@(tr,tc) (TopLeft      row col) = (DownRight ** TopLeft (MPR (Succ row)) (MPR (Succ col)))
moveDownRight h@(hr,hc) t@(tr,tc) (TopMiddle    row col) = (DownRight ** TopMiddle (MPR (Succ row)) (Succ col))
moveDownRight h@(hr,hc) t@(tr,tc) (TopRight     row col) = (Down      ** TopMiddle (MPR (Succ row)) col)
moveDownRight h@(hr,hc) t@(tr,tc) (MiddleLeft   row col) = (DownRight ** MiddleLeft (Succ row) (MPR (Succ col)))
moveDownRight h@(hr,hc) t@(tr,tc) (Covers       row col) = (Stay      ** TopLeft (PMRZr row) (PMRZr col))
moveDownRight h@(hr,hc) t@(tr,tc) (MiddleRight  row col) = (Stay      ** TopMiddle (PMRZr row) col)
moveDownRight h@(hr,hc) t@(tr,tc) (BottomLeft   row col) = (Right     ** MiddleLeft row (MPR (Succ col)))
moveDownRight h@(hr,hc) t@(tr,tc) (BottomMiddle row col) = (Stay      ** MiddleLeft row (PMRZr col))
moveDownRight h@(hr,hc) t@(tr,tc) (BottomRight  row col) = (Stay      ** Covers row col)

public export
move : (dh : Direction) -> (h,t : Pos) -> Touching h t -> (dt ** Touching (movePos dh h) (movePos dt t))
move UpLeft    = moveUpLeft
move Up        = moveUp
move UpRight   = moveUpRight
move Left      = moveLeft
move Stay      = \h@(hr,hc),t@(tr,tc),c => (Stay ** c)
move Right     = moveRight
move DownLeft  = moveDownLeft
move Down      = moveDown
move DownRight = moveDownRight


public export
record Rope where
  constructor MkRope
  head : Pos
  tail : Pos
  touching : Touching head tail

export
Show Rope where
  show (MkRope h t _) = show (h,t)

export
start : Rope
start = MkRope (0,0) (0,0) (Covers (Same 0) (Same 0))

export
moveRope : Direction -> Rope -> Rope
moveRope dirHead (MkRope head tail touching) = case move dirHead head tail touching of
  (dirTail ** touching') => (MkRope (movePos dirHead head) (movePos dirTail tail) touching')

mutual

  public export
  data Long : Type where
    End  : (h,t : Pos)               -> (1 _ : Touching h t)        -> Long
    More : (h   : Pos) -> (t : Long) -> (1 _ : Touching h (head t)) -> Long
 
  public export
  head : Long -> Pos
  head (End h t x)  = h
  head (More h t x) = h

mutual

  export
  startLong : Nat -> Long
  startLong 0     = End (0,0) (0,0) (Covers (Same 0) (Same 0))
  startLong (S k) with (startLong k) proof prf
    _ | l = More (0,0) l (rewrite (sym prf) in (rewrite (startLongHeadLemma k) in (Covers (Same 0) (Same 0))))

  startLongHeadLemma : (n : Nat) -> head (startLong n) === (0,0)
  startLongHeadLemma 0     = Refl
  startLongHeadLemma (S k) = Refl

export
toList : Long -> List Pos
toList (End h t x)  = [h,t]
toList (More h t x) = h :: toList t

export
longTail : Long -> Pos
longTail (End  h t x) = t
longTail (More h t x) = longTail t

public export
Visited : Type
Visited = SortedMap Pos Int

export
VisitedRef : Type
VisitedRef = IORef Visited

export
newVisitedRef : IO VisitedRef
newVisitedRef = newIORef empty

export
getVisited : {auto ref : VisitedRef} -> IO Visited
getVisited {ref} = readIORef ref

export
visit : {auto ref : VisitedRef} -> Pos -> IO ()
visit {ref} pos = modifyIORef ref $ mergeWith (+) (singleton pos 1)
