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
