module Day10.Input

import Day10.Domain

export
testInput : List Instr
testInput =
 [ AddX 15
  , AddX $ 0-11
  , AddX 6
  , AddX $ 0-3
  , AddX 5
  , AddX $ 0-1
  , AddX $ 0-8
  , AddX 13
  , AddX 4
  , Noop
  , AddX $ 0-1
  , AddX 5
  , AddX $ 0-1
  , AddX 5
  , AddX $ 0-1
  , AddX 5
  , AddX $ 0-1
  , AddX 5
  , AddX $ 0-1
  , AddX $ 0-35
  , AddX 1
  , AddX 24
  , AddX $ 0-19
  , AddX 1
  , AddX 16
  , AddX $ 0-11
  , Noop
  , Noop
  , AddX 21
  , AddX $ 0-15
  , Noop
  , Noop
  , AddX $ 0-3
  , AddX 9
  , AddX 1
  , AddX $ 0-3
  , AddX 8
  , AddX 1
  , AddX 5
  , Noop
  , Noop
  , Noop
  , Noop
  , Noop
  , AddX $ 0-36
  , Noop
  , AddX 1
  , AddX 7
  , Noop
  , Noop
  , Noop
  , AddX 2
  , AddX 6
  , Noop
  , Noop
  , Noop
  , Noop
  , Noop
  , AddX 1
  , Noop
  , Noop
  , AddX 7
  , AddX 1
  , Noop
  , AddX $ 0-13
  , AddX 13
  , AddX 7
  , Noop
  , AddX 1
  , AddX $ 0-33
  , Noop
  , Noop
  , Noop
  , AddX 2
  , Noop
  , Noop
  , Noop
  , AddX 8
  , Noop
  , AddX $ 0-1
  , AddX 2
  , AddX 1
  , Noop
  , AddX 17
  , AddX $ 0-9
  , AddX 1
  , AddX 1
  , AddX $ 0-3
  , AddX 11
  , Noop
  , Noop
  , AddX 1
  , Noop
  , AddX 1
  , Noop
  , Noop
  , AddX $ 0-13
  , AddX $ 0-19
  , AddX 1
  , AddX 3
  , AddX 26
  , AddX $ 0-30
  , AddX 12
  , AddX $ 0-1
  , AddX 3
  , AddX 1
  , Noop
  , Noop
  , Noop
  , AddX $ 0-9
  , AddX 18
  , AddX 1
  , AddX 2
  , Noop
  , Noop
  , AddX 9
  , Noop
  , Noop
  , Noop
  , AddX $ 0-1
  , AddX 2
  , AddX $ 0-37
  , AddX 1
  , AddX 3
  , Noop
  , AddX 15
  , AddX $ 0-21
  , AddX 22
  , AddX $ 0-6
  , AddX 1
  , Noop
  , AddX 2
  , AddX 1
  , Noop
  , AddX $ 0-10
  , Noop
  , Noop
  , AddX 20
  , AddX 1
  , AddX 2
  , AddX 2
  , AddX $ 0-6
  , AddX $ 0-11
  , Noop
  , Noop
  , Noop
  ]

export
input : List Instr
input =
  [ Noop
  , Noop
  , Noop
  , AddX 3
  , AddX 20
  , Noop
  , AddX $ 0-12
  , Noop
  , AddX 4
  , Noop
  , Noop
  , Noop
  , AddX 1
  , AddX 2
  , AddX 5
  , AddX 16
  , AddX $ 0-14
  , AddX $ 0-25
  , AddX 30
  , AddX 1
  , Noop
  , AddX 5
  , Noop
  , AddX $ 0-38
  , Noop
  , Noop
  , Noop
  , AddX 3
  , AddX 2
  , Noop
  , Noop
  , Noop
  , AddX 5
  , AddX 5
  , AddX 2
  , AddX 13
  , AddX 6
  , AddX $ 0-16
  , AddX 2
  , AddX 5
  , AddX $ 0-15
  , AddX 16
  , AddX 7
  , Noop
  , AddX $ 0-2
  , AddX 2
  , AddX 5
  , AddX $ 0-39
  , AddX 4
  , AddX $ 0-2
  , AddX 2
  , AddX 7
  , Noop
  , AddX $ 0-2
  , AddX 17
  , AddX $ 0-10
  , Noop
  , Noop
  , AddX 5
  , AddX $ 0-1
  , AddX 6
  , Noop
  , AddX $ 0-2
  , AddX 5
  , AddX $ 0-8
  , AddX 12
  , AddX 3
  , AddX $ 0-2
  , AddX $ 0-19
  , AddX $ 0-16
  , AddX 2
  , AddX 5
  , Noop
  , AddX 25
  , AddX 7
  , AddX $ 0-29
  , AddX 3
  , AddX 4
  , AddX $ 0-4
  , AddX 9
  , Noop
  , AddX 2
  , AddX $ 0-20
  , AddX 23
  , AddX 1
  , Noop
  , AddX 5
  , AddX $ 0-10
  , AddX 14
  , AddX 2
  , AddX $ 0-1
  , AddX $ 0-38
  , Noop
  , AddX 20
  , AddX $ 0-15
  , Noop
  , AddX 7
  , Noop
  , AddX 26
  , AddX $ 0-25
  , AddX 2
  , AddX 7
  , Noop
  , Noop
  , AddX 2
  , AddX $ 0-5
  , AddX 6
  , AddX 5
  , AddX 2
  , AddX 8
  , AddX $ 0-3
  , Noop
  , AddX 3
  , AddX $ 0-2
  , AddX $ 0-38
  , AddX 13
  , AddX $ 0-6
  , Noop
  , AddX 1
  , AddX 5
  , Noop
  , Noop
  , Noop
  , Noop
  , AddX 2
  , Noop
  , Noop
  , AddX 7
  , AddX 3
  , AddX $ 0-2
  , AddX 2
  , AddX 5
  , AddX 2
  , Noop
  , AddX 1
  , AddX 5
  , Noop
  , Noop
  , Noop
  , Noop
  , Noop
  , Noop
  ]
