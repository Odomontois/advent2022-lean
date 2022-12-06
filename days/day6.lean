import Advent.List
import Advent.Read

def prefLength (n: Nat) (s: List Char): Nat :=
  (((tails s).enum.find? (fun xs => differs (xs.snd.take n))).map (·.fst + n)).getD 0
where
differs : List Char -> Bool
| [] => true
| x :: xs => xs.all (· != x) && differs xs


def main : IO  Unit := do
  let inp <- readInput 6
  IO.println (prefLength 4 inp.toList)
  IO.println (prefLength 14 inp.toList)