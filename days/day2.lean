import Advent


open Except (ok error)

def parseChoices1 (code: String): Except String (Char × Char) := do
  let (c1, c2) <- match String.toList code with
    | [c1, _, c2] => ok (c1, c2)
    | _ => error (s!"can't parse {code}")

  let p1 <- match c1 with
    | 'A' => ok 'R'
    | 'B' => ok 'P'
    | 'C' => ok 'S'
    | _ => Except.error (s!"wrong symbol {c1}")

  let p2 <- match c2 with 
    | 'X' => ok 'R'
    | 'Y' => ok 'P'
    | 'Z' => ok 'S'
    | _ => Except.error (s!"wrong symbol {c2}")
  
  return (p1, p2)


def lose (c: Char) := match c with
  | 'R' => 'S' | 'P' => 'R' | _ => 'P'

def win (c: Char) := match c with
  | 'S' => 'R' | 'R' => 'P' | _ => 'S'

def parseChoices2 (code: String): Except String (Char × Char) := do
  let (c1, c2) <- match String.toList code with
    | [c1, _, c2] => ok (c1, c2)
    | _ => error (s!"can't parse {code}")

  let p1 <- match c1 with
    | 'A' => ok 'R'
    | 'B' => ok 'P'
    | 'C' => ok 'S'
    | _ => Except.error (s!"wrong symbol {c1}")

  let p2 <- match c2 with 
    | 'X' => ok (lose p1)
    | 'Y' => ok p1
    | 'Z' => ok (win p1)
    | _ => Except.error (s!"wrong symbol {c2}")
  
  return (p1, p2)

def score (pp: (Char × Char)): Int := 
  let (p1, p2) := pp
  let outcome :=  if p1 == p2 then 3
    else match (p1, p2) with
      | ('R', 'P') | ('P', 'S') | ('S', 'R') => 6
      | _ => 0
  let shape := match p2 with 
      | 'R' => 1 | 'P' => 2 | 'S' => 3 | _ => 0
  
  outcome + shape

def fullScore(inputs: List (Char × Char)) : Int := 
  List.foldl (· + score ·) 0 inputs

def printScore 
  (choiceF: String -> Except String (Char × Char)) 
  (lines: List String): IO Unit := do 
  let inputs <- match List.mapM choiceF lines with
    | error s =>  throw (IO.userError s)
    | ok inputs => pure inputs

  IO.println (fullScore inputs)
 
def main : IO Unit := do
let lines <- readLines 2
printScore parseChoices1 lines 
printScore parseChoices2 lines 