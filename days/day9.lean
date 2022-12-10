import Advent.Function
import Advent.Read
import Advent.List
import Lean
import Lean.Data.HashSet
import Advent.Ord

abbrev Point := Int × Int
abbrev HT := Point × List Point


open Ordering 

open Lean (HashSet)

def signum(x: Int) :Int := match compare x 0 with
| lt => -1
| eq => 0
| gt => 1

def abs(x: Int) := x * signum x

def follow: Point -> Point -> Point
| (hx, hy), t@(tx, ty) => 
  if abs (tx - hx) == 2 || abs (ty - hy) == 2
  then (tx + signum (hx - tx), ty + signum (hy - ty))
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