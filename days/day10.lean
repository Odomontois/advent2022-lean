import Advent.Read
import Advent.Show

def parse (cmd: String): List (Option Int) :=
  match cmd.splitOn with 
  | ["addx", s] => [none, s.toInt?]
  | _ => [none]

structure Cathod where
  x: Int
  tick: Nat
  info: List Int
deriving Lean.ToJson

def Cathod.init: Cathod := ⟨1, 1, []⟩ 

def handle (save: Nat -> Bool) (cmd: Option Int): StateM Cathod Unit
  | ⟨ x, tick, info ⟩ => 
    let info' := if save tick then x * tick :: info else info
    let dx := cmd.getD 0
    let cathod := ⟨x + dx, tick + 1, info'⟩
    ((), cathod)

def main : IO Unit := do
  let inps <- readLines 10
  let cmds := inps.bind parse
  let cycles := [20, 60, 100, 140, 180, 220]
  let (_, final) := cmds.mapM (handle (cycles.contains ·)) Cathod.init
  IO.println final
  IO.println (final.info.foldl (· + ·) 0)

