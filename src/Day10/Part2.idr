module Day10.Part2

import Day10.Domain
import Data.Buffer


partial
createScreen : IO (CPUProbe, IO ())
createScreen = do
  Just buffer <- newBuffer 240
  traverse_ (\idx => setBits8 buffer idx 0) [0..239]
  pure (mkCPUProbe (setPixel buffer), renderScreen buffer)
  where
    Pixel : Type
    Pixel = Bits8

    calcPixel : CPU -> Pixel
    calcPixel cpu =
      let col = (cpu.cycle - 1) `mod` 40
      in if (abs (cpu.register - col) > 1)
            then 0 -- Pixel is lit
            else 1 -- Pixel is dark

    renderPixel : Pixel -> IO ()
    renderPixel 0 = putStr "."
    renderPixel 1 = putStr "#"
    renderPixel _ = putStr "?"

    renderScreen : Buffer -> IO ()
    renderScreen buffer = do
      traverse_ (\idx => renderPixel !(getBits8 buffer idx)) [0   ..  39]; putStrLn ""
      traverse_ (\idx => renderPixel !(getBits8 buffer idx)) [40  ..  79]; putStrLn ""
      traverse_ (\idx => renderPixel !(getBits8 buffer idx)) [80  .. 119]; putStrLn ""
      traverse_ (\idx => renderPixel !(getBits8 buffer idx)) [120 .. 159]; putStrLn ""
      traverse_ (\idx => renderPixel !(getBits8 buffer idx)) [160 .. 199]; putStrLn ""
      traverse_ (\idx => renderPixel !(getBits8 buffer idx)) [200 .. 239]; putStrLn ""
      pure ()

    setPixel : Buffer -> CPU -> IO ()
    setPixel buffer cpu = 
      if (cpu.cycle <= 240)
        then setBits8 buffer (cpu.cycle - 1) (calcPixel cpu)
        else pure ()

export
partial
part2 : List Instr -> IO ()
part2 program = do
  (screen, renderScreen) <- createScreen
  _ <- runProgram {probe=screen} program init
  renderScreen

{-
###..#.....##..####.#..#..##..####..##..
#..#.#....#..#.#....#.#..#..#....#.#..#.
#..#.#....#....###..##...#..#...#..#....
###..#....#.##.#....#.#..####..#...#.##.
#....#....#..#.#....#.#..#..#.#....#..#.
#....####..###.#....#..#.#..#.####..###.
-}
