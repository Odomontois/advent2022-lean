import Lean
import Advent

def calcWeights(ss: List String) (acc: List Int) (cur: Int) : List Int := 
  match ss with 
    | List.nil => cur :: acc
    | List.cons h rest => 
      if h == "" then calcWeights rest (cur :: acc) 0
      else match h.toInt? with 
        | some x => calcWeights rest acc (cur + x)
        | none => []

def top1 (s: String) : Int := 
  let ws := calcWeights (String.split s Char.isWhitespace) [] 0
  (List.maximum? ws).getD 0

def top3 (s: String) : Int := 
  let ws := calcWeights (String.split s Char.isWhitespace) [] 0
  let wsa := List.take 3 (Array.toList (Array.qsort (List.toArray ws) (· > ·)))
  wsa.sum

def main : IO Unit := do
  let lines <- readInput 1
  IO.println (top1 lines)
  IO.println (top3 lines)
  return () 
