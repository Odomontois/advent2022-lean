import Advent.Read
import Lean

def charCode (c: Char) : Nat := 
  if c <= 'Z' then c.toNat - 'A'.toNat + 27 else c.toNat - 'a'.toNat + 1

def codeArray (s: String): Array Bool := 
  let init := Array.mkArray 53 false
  s.foldl (fun arr c => arr.set! (charCode c) true) init 

def intersect (ca1: Array Bool) (ca2: Array Bool): Array Bool := 
  ca1.mapIdx (fun i x => x && ca2.getD i false)

def findCommon(s: String) (ca: Array Bool): Nat := 
  let codes := s.toList.map charCode
  (codes.find? ca.get!).getD 0

def commonChar (s: String) : Nat :=
  let k := s.length / 2
  let ca := codeArray (s.take k)
  findCommon (s.drop k) ca

def group (l: List α) (n: Nat): List (List α) := 
  loop l n [] []
where
  loop : List α -> Nat ->  List α -> List (List α)  -> List (List α)
  | [], _, gacc, acc=> (gacc.reverse :: acc).reverse
  | x :: xs, 0, gacc, acc => loop xs (n - 1)  [x] (gacc.reverse :: acc) 
  | x :: xs, rem + 1, gacc, acc => loop xs rem (x :: gacc) acc  

def common3 (l: List String): Nat := 
  let init := Array.mkArray 53 true
  let i3 := (l.map codeArray).foldl intersect init
  (i3.findIdx? (·)).getD 0

def main : IO Unit := do
  let lines <- readLines 3
  let commons := lines.map commonChar
  IO.println (commons.foldl (· + ·) 0)
  let grouped := group lines 3
  let c3s := grouped.map common3
  IO.println c3s
  IO.println (c3s.foldl (· + ·) 0)
  