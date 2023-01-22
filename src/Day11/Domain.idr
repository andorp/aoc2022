module Day11.Domain

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

-- Sketch of the solution:
-- A list of monkeys, that describes their brain and the actual items.
-- A monkey does not pass any items to itself.
-- Filter all the items that in the monkey's hand and add at the end of the list
-- As we don't have too much items a simple list addition would work.
-- We should run the simulation in IO as for the quick lookup and state modification IORefs are better.

public export
Item : Type
Item = Int

||| The brain of the nth monkey
public export
record MonkeyBrain (n : Nat) where
  constructor MkBrain
  divisible : Int
  operation : Item -> Item
  ifTrue    : Fin n
  ifFalse   : Fin n

public export
record Monkey (n : Nat) where
  constructor MkMonkey
  brain : MonkeyBrain n
  items : List Item

namespace Worrying

  export
  WorryChange : Type
  WorryChange = Item -> Item

  export
  mkWorryChange : (Item -> Item) -> WorryChange
  mkWorryChange = id

  export
  calcWorry : WorryChange -> Item -> Item
  calcWorry f i = f i

-- Checks the item, tests it, and decreases the worry level.
inspects : {auto worrying : WorryChange} -> MonkeyBrain n -> List Item -> (List Item, List Item)
inspects {worrying} brain items
  = TailRec.partition pred
  $ map (calcWorry worrying . brain.operation)
  $ items
  where
    pred : Item -> Bool
    pred i = i `mod` brain.divisible == 0

namespace Simulation

  MonkeyItems : Nat -> Type
  MonkeyItems x = Vect x (MonkeyBrain x, IORef (List Item), IORef Int)

  parameters
    {auto x           : Nat}
    {auto monkeyItems : MonkeyItems x}
    {auto worrying    : WorryChange}

    mostActiveMonkeys : IO Int
    mostActiveMonkeys = do
      bestTwoRef <- newIORef (the (List Int) [])
      let addNewItem : (Int -> IO ()) = \x => do
            bestTwo <- readIORef bestTwoRef
            writeIORef bestTwoRef $ TailRec.take 2 $ reverse $ sort (x :: bestTwo)
      traverse_
        (\(brain, items, inspected) => addNewItem !(readIORef inspected))
        monkeyItems
      map product $ readIORef bestTwoRef

    showMonkeyActivity : IO ()
    showMonkeyActivity = do
      traverse_
        (\(brain, items, inspected) => do
          putStrLn "Monkey inspected: \{show !(readIORef inspected)}"
--          putStrLn "Monkey items: \{show !(readIORef items)}"
        )
        monkeyItems

    throwToMonkey : Fin x -> List Item -> IO ()
    throwToMonkey idx newItems = do
      let (brain,itemsRef,inspects) = index idx monkeyItems
      items <- readIORef itemsRef
      writeIORef itemsRef (items ++ newItems)

    loop : Nat -> Nat -> IO ()
    loop 0 c = do
      putStrLn "Done."
      showMonkeyActivity
      printLn !(mostActiveMonkeys)
    loop (S m) c = do
      printLn $ "Round \{show c}"
      when (c `elem` (the (List Nat) [0,20,1000,2000,3000,4000,5000,6000,7000,8000,9000,10000])) $ do
        printLn $ "Round \{show c}"
        showMonkeyActivity
      traverse_ 
        (\(brain, itemsRef, inspectRef) => do
          items <- readIORef itemsRef
          inspected <- readIORef inspectRef
          let (trues, falses) = inspects brain items
          writeIORef inspectRef (inspected + cast (TailRec.length items))
          writeIORef itemsRef []
          throwToMonkey brain.ifTrue trues
          throwToMonkey brain.ifFalse falses
        )
        monkeyItems
      loop m (S c)

  export
  simulation : {auto worrying : WorryChange} -> {n : Nat} -> Vect n (Monkey n) -> Nat -> IO ()
  simulation {n} monkeys rounds = do
    monkeyItems
      <- traverse
            (\monkey => do
              itemsRef   <- newIORef monkey.items
              inspectRef <- newIORef (the Int 0)
              pure (monkey.brain, itemsRef, inspectRef))
            monkeys
    loop {x=n} rounds 0
