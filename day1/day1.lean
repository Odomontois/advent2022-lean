import Lean

def digitCode (c: Char): Int := 
  Char.toNat c - Char.toNat '0'

def parseIntRec (s: List Char) (acc: Int): Option Int :=   
  match s with 
    | [] => acc
    | x :: rest =>
      if Char.isDigit x then 
        parseIntRec rest (acc * 10 + digitCode x)
      else Option.none

def parseInt (s: String): Option Int := parseIntRec (String.toList s) 0


def calcWeights(ss: List String) (acc: List Int) (cur: Int) : List Int := 
  match ss with 
    | List.nil => cur :: acc
    | List.cons h rest => 
      if h == "" then calcWeights rest (cur :: acc) 0
      else match parseInt h with 
        | some x => calcWeights rest acc (cur + x)
        | none => []

def top1 (s: String) : Int := 
  let ws := calcWeights (String.split s Char.isWhitespace) [] 0
  Option.getD (List.maximum? ws) 0

def top3 (s: String) : Int := 
  let ws := calcWeights (String.split s Char.isWhitespace) [] 0
  let wsa := List.take 3 (Array.toList (Array.qsort (List.toArray ws) (· > ·)))
  List.foldl (· + ·) 0 wsa

def main : IO Unit := do
  let lines <- IO.FS.readFile "./day1/test-input.txt"
  IO.println (top1 lines)
  IO.println (top3 lines)
  return ()

-- #eval 

