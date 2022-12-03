import Advent.Read
import Lean

def charCode (c: Char) : Nat := 
  if c <= 'Z' then c.toNat - 'A'.toNat + 27 else c.toNat - 'a'.toNat + 1

def codeArray (s: String): Array Bool := 
  let init := Array.mkArray 53 false
  s.foldl (fun arr c => arr.set! (charCode c) true) init 

def findCommon(s: String) (ca: Array Bool): Nat := 
  let codes := s.toList.map charCode
  (codes.find? ca.get!).getD 0

def commonChar (s: String) : Nat :=
  let k := s.length / 2
  let ca := codeArray (s.take k)
  findCommon (s.drop k) ca


def main : IO Unit := do
  let lines <- readLines 3
  let commons := lines.map commonChar
  IO.println (commons)
  IO.println (commons.foldl (· + ·) 0)
  