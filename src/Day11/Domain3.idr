module Day11.Domain3

import Data.Fin
import Data.Vect
import Data.SortedMap
import Data.IORef
import Data.List
import Data.List1
import Data.List.TailRec
import Data.List1.Quantifiers
import Data.List.Quantifiers
import Decidable.Equality

public export
Item : Type
Item = Int

public export
record MonkeyBrain (item : Type) (n : Nat) where
  constructor MkBrain
  divisible : Int
  operation : item -> item
  ifTrue    : Fin n
  ifFalse   : Fin n

public export
interface IsDivisible item where
  isDivible : item -> Int -> Bool

export
IsDivisible Int where
  isDivible i d = i `mod` d == 0

public export
record Monkey (item : Type) (n : Nat) where
  constructor MkMonkey
  brain : MonkeyBrain item n
  items : List item

-- Checks the item, tests it, and decreases the worry level.
inspects : (IsDivisible item) => (b : MonkeyBrain item n) -> (item -> item) -> List item -> (List item, List item)
inspects b worryChange items
  = TailRec.partition (flip isDivible b.divisible)
  $ map (worryChange . b.operation)
  $ items

namespace Worrying

  export
  WorryChange : Type -> Type
  WorryChange item = item -> item

  export
  mkWorryChange : (item -> item) -> WorryChange item
  mkWorryChange = id

  export
  calcWorry : WorryChange item -> item -> item
  calcWorry f i = f i

namespace Simulation

  MonkeyItems : Type -> Nat -> Type
  MonkeyItems i x = Vect x (MonkeyBrain i x, IORef (List i), IORef Int)

  parameters
    {auto x             : Nat}
    {auto item          : Type}
    {auto monkeyItems   : MonkeyItems item x}
    {auto worrying      : WorryChange item}
    {auto showItem      : Show item}
    {auto divisibleItem : IsDivisible item}

    mostActiveMonkeys : IO Int
    mostActiveMonkeys = do
      bestTwoRef <- newIORef (the (List Int) [])
      let addNewItem : (Int -> IO ()) = \x => do
            bestTwo <- readIORef bestTwoRef
            writeIORef bestTwoRef $ TailRec.take 2 $ reverse $ sort (x :: bestTwo) -- TODO: Improve
      traverse_
        (\case
            (brain, items, inspected) => addNewItem !(readIORef inspected))
        monkeyItems
      map product $ readIORef bestTwoRef

    showMonkeyActivity : IO ()
    showMonkeyActivity = do
      traverse_
        (\(brain, items, inspected) => do
          putStrLn "Monkey inspected: \{show !(readIORef inspected)}"
          putStrLn "Monkey items: \{show !(readIORef items)}"
        )
        monkeyItems

    throwToMonkey : Fin x -> List item -> IO ()
    throwToMonkey idx newItems = do
      let (brain,itemsRef,inspected) = index idx monkeyItems
      items <- readIORef itemsRef
      writeIORef itemsRef (items ++ newItems)

    loop : Nat -> Int -> IO ()
    loop 0 c = do
      putStrLn "Done."
      showMonkeyActivity
      printLn !(mostActiveMonkeys)
      pure ()
    loop (S m) c = do
      when (c `elem` (the (List Int) [0,20,1000,2000,3000,4000,5000,6000,7000,8000,9000,10000])) $ do
        printLn $ "Round \{show c}"
        showMonkeyActivity
      traverse_ 
        (\(brain, itemsRef, inspectRef) => do
          items <- readIORef itemsRef
          inspected <- readIORef inspectRef
          let (trues, falses) = inspects brain (calcWorry worrying) items
          writeIORef inspectRef (inspected + cast (TailRec.length items))
          writeIORef itemsRef []
          throwToMonkey brain.ifTrue trues
          throwToMonkey brain.ifFalse falses
        )
        monkeyItems
      loop m (1 + c)

  export
  simulation
    :  (item : Type)
    -> (worrying : WorryChange item)
    -> (Show item, IsDivisible item)
    => {n : Nat}
    -> (monkeys : Vect n (Monkey item n))
    -> (rounds : Nat)
    -> IO ()
  simulation item worrying {n} monkeys rounds = do
    monkeyItems
      <- traverse
            (\monkey => do
              itemsRef   <- newIORef monkey.items
              inspectRef <- newIORef (the Int 0)
              pure (monkey.brain, itemsRef, inspectRef))
            monkeys
    loop {x=n} {item=item} rounds 0
