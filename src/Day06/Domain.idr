module Day06.Domain

import Data.Vect
import Data.So
import Data.Vect.Quantifiers

public export
sizeOfBlock : Nat
sizeOfBlock = 4

public export
Block : Type
Block = Vect sizeOfBlock Char

public export
sizeOfMessage : Nat
sizeOfMessage = 14

public export
Message : Type
Message = Vect sizeOfMessage Char

contains : Char -> Vect n Char -> Bool
contains c [] = False
contains c (x :: xs) = if c == x then True else contains c xs

data SetLike : (xs : Vect n Char) -> Type where
  Nil  : SetLike []
  Cons : (x : Char) -> {new : So (not (contains x xs))} -> SetLike xs -> SetLike (x :: xs)

contradictionOnSo : So x -> x === False -> a
contradictionOnSo Oh Refl impossible

isSetLike : (xs : Vect n Char) -> Dec (SetLike xs)
isSetLike [] = Yes []
isSetLike (x :: xs) with (not (contains x xs)) proof nc
  _ | False = No (\(Cons y {new} ys) => contradictionOnSo new nc)
  _ | True with (isSetLike xs)
    _ | No contra = No (\(Cons y ys) => contra ys)
    _ | Yes vs = Yes (Cons x {new = eqToSo nc} vs)

export
data StartOfPacket : Block -> Type where
  StartB : (validity : SetLike b) -> StartOfPacket b

export
isStartOfPacket : (b : Block) -> Dec (StartOfPacket b)
isStartOfPacket b with (isSetLike b)
  _ | Yes   valid = Yes (StartB valid)
  _ | No notValid = No (\(StartB assumeValid) => notValid assumeValid)

export
data StartOfMessage : Message -> Type where
  StartM : (validity : SetLike m) -> StartOfMessage m

export
isStartOfMessage : (m : Message) -> Dec (StartOfMessage m)
isStartOfMessage m with (isSetLike m)
  _ | Yes   valid = Yes (StartM valid)
  _ | No notValid = No (\(StartM assumeValid) => notValid assumeValid)
