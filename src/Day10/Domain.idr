module Day10.Domain

import Data.DPair
import Control.WellFounded
import Data.Buffer
import Data.IORef

%default total

public export
Cycle : Type
Cycle = Int

public export
data Instr
  = AddX Int
  | Noop

cost : Instr -> Nat
cost (AddX _) = 1
cost Noop     = 0

public export
record CPU where
  constructor MkCPU
  register : Int
  cycle    : Cycle

export
Show CPU where
  show (MkCPU r c) = show (c,r)

export
init : CPU
init = MkCPU 1 1

namespace Probe

  export
  CPUProbe : Type
  CPUProbe = CPU -> IO ()

  export
  mkCPUProbe : (CPU -> IO ()) -> CPUProbe
  mkCPUProbe x = x

  export
  run : CPUProbe -> CPU -> IO ()
  run f c = f c


data Execution = Start | Running Instr Nat | Done Instr | Finished

data Transition : Execution -> Execution -> Type where
  In : (i : Instr) -> (n : Nat) -> Transition Start (Running i n)
  St : Transition (Running i (S n)) (Running i n)
  Dn : Transition (Running i 0) (Done i)
  Ex : Transition (Done i) Finished

data CPUMonad : Execution -> Execution -> Type where
  (>>) : {1 m : Execution} -> CPUMonad s m -> CPUMonad m e -> CPUMonad s e
  Tick : Transition s e -> CPUMonad s e

compileRun : {i : Instr} -> {n : Nat} -> CPUMonad (Running i n) (Done i)
compileRun {n=0}     = Tick Dn
compileRun {n=(S k)} = (Tick St) >> (compileRun {n=k})

compile : Instr -> CPUMonad Start Finished
compile i = do
  Tick (In i (cost i))
  compileRun
  Tick Ex

parameters
  {auto probe : CPUProbe}

  checkCPU : Execution -> CPU -> IO ()
  checkCPU (Running _ _) cpu = run probe cpu
  checkCPU _             _   = pure ()

  transition : (1 s,e : Execution) -> (1 _ : Transition s e) -> CPU -> CPU
  transition Start                (Running i n)    (In i n) cpu = cpu
  transition (Running i (S n))    (Running i n)    St       cpu = ({cycle $= (+1)} cpu)
  transition (Running (AddX x) 0) (Done (AddX x))  Dn       cpu = ({cycle $= (+1), register $= (+x)} cpu)
  transition (Running Noop 0)     (Done Noop)      Dn       cpu = ({cycle $= (+1)} cpu)
  transition (Done i)             Finished         Ex       cpu = cpu

  runCPU : {s,e : Execution} -> CPU -> CPUMonad s e -> IO CPU
  runCPU cpu (m >> k) = do
    cpu' <- runCPU cpu m
    runCPU cpu' k
  runCPU {s,e} cpu (Tick t) = do
    checkCPU s cpu
    pure $ transition s e t cpu

  runInstr : Instr -> CPU -> IO CPU
  runInstr i cpu = runCPU cpu $ compile i

  export
  runProgram : List Instr -> CPU -> IO CPU
  runProgram [] cpu = pure cpu
  runProgram (i::is) cpu = do
    cpu' <- runInstr i cpu
    runProgram is cpu'
