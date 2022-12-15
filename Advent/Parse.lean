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

def ParseState := String
abbrev Parse α := EStateM ParseState String α

instance : EStateM.Backtrackable String ParseState where
  save s := s
  restore s _ := s

open EStateM.Result 
namespace Parse
def fromOption (err: Unit -> String): Option α -> Parse α
| some x => pure x
| none => throw <| err ()

def str (txt: String): Parse Unit := λ s => 
  if s.startsWith txt 
  then  ok () <| s.drop txt.length
  else error s s!"expecting {txt}"
    

def take (i: Nat): Parse String := λ s => ok (s.take i) (s.drop i)


def segment (p: Char -> Bool) (err: String -> String) (parse: String -> Option α): Parse α := do
  let s <- EStateM.get
  let i := s.nextWhile p 0
  let s <- take i.byteIdx
  fromOption (λ_ => err s) (parse s) 

def nat : Parse Nat := segment (·.isDigit) (s!"{·} is not a natural") (·.toNat!)

def int : Parse Int := segment (λ c => c.isDigit || c == '-') (s!"{·} is not an integer") (·.toInt?)

def ws: Parse Unit := EStateM.modifyGet ((), ·.trimLeft)

partial def rep (p: Parse α): Parse (List α) := do
  let a <- try p catch _ => return []
  let as <- p.rep
  return  a :: as

def repSep (p: Parse α) (sep: String): Parse (List α) := do
  let first <- try p catch _ => return []
  let rest <- (str sep *> p).rep
  return first :: rest
  

def runE (p: Parse α) (s: String):  (String × Except String α) := 
  match p s with
  | ok a s' => (s', pure a)
  | error err s' => (s', throw err)
end Parse