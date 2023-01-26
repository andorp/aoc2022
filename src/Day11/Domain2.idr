module Day11.Domain2

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

-- namespace Modulo

public export
Item : Type
Item = Int

||| The brain of the nth monkey
public export
record MonkeyBrain (modulo : Int) (n : Nat) where
  constructor MkBrain
  divisible : Int
  operation : Item -> Item
  ifTrue    : Fin n
  ifFalse   : Fin n

relabelModuloBrain : (m : Int) -> MonkeyBrain a n -> MonkeyBrain m n
relabelModuloBrain m b = MkBrain
  { divisible = b.divisible
  , operation = b.operation
  , ifTrue    = b.ifTrue
  , ifFalse   = b.ifFalse
  }

public export
record Monkey (modulo : Int) (n : Nat) where
  constructor MkMonkey
  brain : MonkeyBrain modulo n
  items : List Item

relabelModuloMonkey : (m : Int) -> Monkey a n -> Monkey m n
relabelModuloMonkey m k = MkMonkey
  { brain = relabelModuloBrain m k.brain
  , items = k.items
  }

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
inspects : {modulo : Int} -> (b : MonkeyBrain modulo n) -> List Item -> (List Item, List Item)
inspects {modulo} b items
  = TailRec.partition isDivible
  $ map (\x => (b.operation x) `mod` modulo)
  $ items
  where
    isDivible : Item -> Bool
    isDivible i = i `mod` b.divisible == 0


namespace Simulation

  MonkeyItems : Int -> Nat -> Type
  MonkeyItems m x = Vect x (MonkeyBrain m x, IORef (List Item), IORef Int)

  parameters
    {auto x           : Nat}
    {auto modulo      : Int}
    {auto monkeyItems : MonkeyItems modulo x}
    {auto worrying    : WorryChange}

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

    throwToMonkey : Fin x -> List Item -> IO ()
    throwToMonkey idx newItems = do
      let (brain,itemsRef,inspects) = index idx monkeyItems
      items <- readIORef itemsRef
      writeIORef itemsRef (items ++ newItems)

    loop : Nat -> Int -> IO ()
    loop 0 c = do
      putStrLn "Done."
      showMonkeyActivity
      printLn !(mostActiveMonkeys)
    loop (S m) c = do
      when (c `elem` (the (List Int) [0,20,1000,2000,3000,4000,5000,6000,7000,8000,9000,10000])) $ do
        printLn $ "Round \{show c}"
        showMonkeyActivity
      traverse_ 
        (\(brain, itemsRef, inspectRef) => do
          items <- readIORef itemsRef
          inspected <- readIORef inspectRef
          let (trues, falses) = inspects {modulo=modulo} brain items
          writeIORef inspectRef (inspected + cast (TailRec.length items))
          writeIORef itemsRef []
          throwToMonkey brain.ifTrue trues
          throwToMonkey brain.ifFalse falses
        )
        monkeyItems
      loop m (1 + c)

  export
  simulation : (worrying : WorryChange) -> {n : Nat} -> Vect n (Monkey 0 n) -> Nat -> IO ()
  simulation worrying {n} monkeys0 rounds = do
    let c : Int := product $ map (\m => m.brain.divisible) monkeys0
    let monkeys : Vect n (Monkey c n) := map (relabelModuloMonkey c) monkeys0
    monkeyItems
      <- traverse
            (\monkey => do
              itemsRef   <- newIORef monkey.items
              inspectRef <- newIORef (the Int 0)
              pure (monkey.brain, itemsRef, inspectRef))
            monkeys
    loop {x=n} {modulo=c} rounds 0
