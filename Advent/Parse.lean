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

instance {α}: HOr (Parse α) (Parse α) (Parse α) where
  hOr x y := try x catch _ => y

variable (p: Parse α)

def strAs (txt: String) (x : α): Parse α := λ s => 
  if s.startsWith txt 
  then ok x <| s.drop txt.length
  else error s!"expecting '{txt}'" s

def str (txt: String): Parse Unit := strAs txt ()

def choose (variants: List (String × α)): Parse α :=
  let expected := fun _ => String.join <| (variants.map (·.fst) ).intersperse "|"
  variants.foldl (fun acc (s, x) => acc ||| strAs s x) (throw s!"expected on of {expected ()}")

def strChain (txts: List (List String)): Parse Unit := 
  txts.forM (·.foldl (· ||| str ·) (throw ""))

def take (i: Nat): Parse String := λ s => ok (s.take i) (s.drop i)

def seg (p: Char -> Bool): Parse String := do
  let s <- EStateM.get
  let i := s.nextWhile p 0
  if i == 0 then throw s!"incorrect character"
  take i.byteIdx

def attempt (err: β -> String) (parse: β -> Option α) (b: β) : Parse α := match parse b with
| some x => pure x
| none => throw <| err b

def int : Parse Int := seg (λ c => c.isDigit || c == '-') >>= attempt (s!"'{·}' is not an integer") (·.toInt?)
def nat : Parse Nat := seg (·.isDigit) >>= attempt (s!"'{·}' is not a natural") (·.toNat!)

def ws: Parse Unit := EStateM.modifyGet ((), ·.trimLeft)

partial def rep (p: Parse α): Parse (List α) := do
  let a <- try p catch _ => return []
  let as <- p.rep
  return a :: as

def opt: Parse (Option α) := 
  try some <$> p catch _ => return none

def optu: Parse Unit := try  _ <- p catch _ => return

def repSep (sep: String): Parse (List α) := do
  let first <- try p catch _ => return []
  let rest <- (str sep *> p).rep
  return first :: rest

def repSep! (sep: String): Parse (List α) := do
  let first <- p
  let rest <- (str sep *> p).rep
  return first :: rest

def runE (s: String):  (String × Except String α) := 
  match p s with
  | ok a s' => (s', pure a)
  | error s' err => (s', throw err)

def runIO (s: String): IO α :=
  match p s with 
  | ok a _ => (return a)
  | error (err: String) s' => throw <| IO.userError s!" error \"{err}\" during parsing \"{s'}\""
end Parse