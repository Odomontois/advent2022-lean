import Advent
import Lean
import Std

abbrev Point := Int × Int
abbrev HT := Point × List Point



open Lean (HashSet)

def follow: Point -> Point -> Point
| (hx, hy), t@(tx, ty) => 
  if (tx - hx).abs == 2 || (ty - hy).abs == 2
  then (tx + (hx - tx).signum, ty + (hy - ty).signum)
  else t

def followAll(head: Point) (tails: List Point): List Point :=
  (tails.scanl follow head).tail!


def move: HT -> Char -> HT
| ((hx, hy), t), c => 
  let h' := match c with 
  | 'L' => (hx - 1, hy)
  | 'R' => (hx + 1, hy)
  | 'U' => (hx, hy + 1)
  | 'D' => (hx, hy - 1)
  | _   => (hx, hy)
  let t' := followAll h' t
  (h', t')

def parse(s: String): Char × Nat := (s.get! 0, (s.drop 2).toNat!)

def tailPositions(count: Nat) (ms: List Char):= 
  let init: HT := ((0, 0), List.replicate count (0, 0))
  ms.scanl move init |> List.map (·.snd.getLast!)


def countPoss (count: Nat) (moves: List Char) :=
  let poss := (tailPositions count moves)
  let ps := HashSet.empty.insertMany poss
  ps.size

def main : IO Unit := do
  let lines <- readLines 9
  let ms := lines.map parse
  let allMs := ms.bind (fun (c, n) => List.replicate n c)

  IO.println (countPoss 1 allMs)
  IO.println (countPoss 9 allMs)