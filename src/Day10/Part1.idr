module Day10.Part1

import Data.IORef
import Day10.Domain

%default total

createSummary : List Int -> IO (CPUProbe, IO Int)
createSummary xs = do
  ref <- newIORef 0
  pure (mkCPUProbe (checkList ref), readResult ref)
  where
    readResult : IORef Int -> IO Int
    readResult = readIORef

    checkList : IORef Int -> CPU -> IO ()
    checkList ref cpu =
      if elem cpu.cycle xs
        then do
          n <- readIORef ref
          writeIORef ref (n + (cpu.cycle * cpu.register))
        else pure ()

export
part1 : List Instr -> IO Int
part1 program = do
  (probe, readProbe) <- createSummary [20,60,100,140,180,220]
  _ <- runProgram {probe=probe} program init
  readProbe
