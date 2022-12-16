import Advent
import Std

notation "Move" => Nat × Nat × Nat
notation "Stack" => List (Option Char)
notation "Stacks" => Array (List Char)


def parseStackLine (s: String): Option Stack := 
  if s.startsWith " 1" then none else (s.toList.group 4).map parse
where 
  parse: List Char -> Option Char
  | '[' :: c :: ']' :: _  => c
  | _ => none

def parseStacks (acc: List Stack): List String -> Stacks × List String
  | line :: rest => match parseStackLine line with
    | some line  => parseStacks (line :: acc) rest
    | none       => final rest
  | [] =>  final [] 
where final (rem: List String) := ((acc.transpose.reverse.map (·.filterMap (·))).toArray, rem)


def parseMove (s: String): Option Move := 
  match s.splitOn " " with
  | ["move", x, "from", y, "to", z] => (x.toNat!, y.toNat!, z.toNat!)
  | _ => none

def applyMove (rev: Bool := true) (s: Stacks)  : Move -> Stacks
  | (cnt, si + 1, ti + 1) =>
    let taken := s[si]!.take cnt
    let dropped := if rev then taken.reverse else taken
    (s.modify ti (dropped ++ ·)).modify si (·.drop cnt)
  | _ => s


def main: IO Unit := do
  let inp <- readLines 5
  let (stacks, rem) := parseStacks [] inp
  let moves := rem.filterMap parseMove
  let result1 := moves.foldl applyMove stacks
  let result2 := moves.foldl (applyMove false) stacks
  let resCode1 := String.mk (result1.toList.map (·.head!))
  let resCode2 := String.mk (result2.toList.map (·.head!))
  IO.println resCode1
  IO.println resCode2


  

   