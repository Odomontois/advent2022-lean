import Advent

inductive DDigit (base: Nat)
  | Z
  | DP (d: Fin base)
  | DN (d: Fin base)
deriving Repr, BEq, Inhabited

instance {base}: ToString (DDigit base) where
  toString 
  | .Z => "0"
  | .DP x => toString <| (x : Nat) + 1
  | .DN x => "-" ++ (toString <| (x : Nat) + 1)

def DoubleSys base := Array (DDigit base)
namespace DoubleSys
  instance {base}: BEq (DoubleSys base) where beq (x: Array _) y := x == y
  instance {base}: Inhabited (DoubleSys base) where default := Array.empty
  instance {base}: ToString (DoubleSys base) where 
    toString := Array.foldl (·.append <| char · |> (·.push '|')) ""
  where 
    char
    | .Z => "0"
    | .DP d => s!"{d.succ}"
    | .DN d => s!"-{d.succ}"

  instance {base}: Coe (DoubleSys base) Nat where
    coe := Array.foldl addDig 0
  where
    base' := base * 2 + 1 
    addDig n
    | .Z => n * base'
    | .DP d => n * base' + d + 1
    | .DN d => n * base' - d - 1 

  instance {base}: Coe Nat (DoubleSys base) where
    coe x := go Array.empty x x
  where
    base' := base * 2 + 1
    go acc x
    | 0 => acc.reverse
    | fuel + 1 => 
      if x == 0 then acc.reverse else
      let r := x % base'
      let x := x / base'
      let d := match r with
        | 0 => DDigit.Z
        | r + 1 => 
          if p: r < base then DDigit.DP ⟨ r, p ⟩
          else let r := 2 * base - 1 - r
               if p: r < base then DDigit.DN ⟨ r, p ⟩
               else DDigit.Z 
      let x := if let .DN _ := d then x + 1 else x
      go (acc.push d) x fuel


end DoubleSys


abbrev SNAFU := DoubleSys 2

def readSnafu (s: String): Option SNAFU := 
  s.toList.toArray.mapM go
where 
  go: Char -> Option (DDigit 2)
  | '-' => some <| DDigit.DN 0
  | '=' => some <| DDigit.DN 1
  | '0' => some <| DDigit.Z
  | '1' => some <| DDigit.DP 0
  | '2' => some <| DDigit.DP 1
  | _   => none

def writeSnafu : SNAFU -> String := 
  String.mk ∘ Array.toList ∘ Array.map toChar
where 
  toChar
  | DDigit.DN 0 => '-'
  | DDigit.DN 1 => '='
  | DDigit.Z => '0'
  | DDigit.DP 0 => '1'
  | DDigit.DP 1 => '2'

def main: IO Unit := do 
  let lines <- readLines 25
  let snafus := (lines.mapM readSnafu).get!
  snafus.forM IO.println
  let nats: List Nat := snafus.map <| λ (x: SNAFU) => ↑x
  nats.forM IO.println
  let back := nats.map (fun (x: Nat) => (x: SNAFU))
  if back == snafus then IO.println "OK!"
  let s := nats.sum
  IO.println s
  IO.println <| writeSnafu s
