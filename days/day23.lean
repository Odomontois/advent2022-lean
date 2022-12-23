import Advent
import Std


def showMatrix (m: Matrix Char): IO Unit := m.forM <| fun row => IO.println <| String.mk row.toList

def last [Inhabited α] (arr: Array α): α := arr[arr.size - 1]!

def frame (cnt: Nat) (el: α) (m: Matrix α): Matrix α := 
  let k := m[0]!.size + 2 * cnt
  let rows := Array.mkArray cnt <| Array.mkArray k el 
  let elems := Array.mkArray cnt el
  let m := m.map <| (elems ++ · ++ elems)
  rows ++ m ++ rows

def hasBound (m: Matrix Char): Bool := 
  if m[0]!.any (· == '#') then  true
  else if (last m).any (· == '#') then true
  else m.any (fun row => row[0]! == '#' || last row == '#')

def step' (m: Matrix Char) (round: Fin 4): IO (Matrix Char × Bool) := do
  let mut m' :=  m
  let mut f := false
  (m', _) <- hashes (m', false) <| tryStep true
  (m', f) <- hashes (m', false) <| tryStep false

  return (m'.map (·.map (λ c => if c == '!' then '.' else c)), f)
where 
  hashes {w α} [Monad w] (x: α) (f: α -> Nat -> Nat -> w α) : w α := do
    let mut x := x
    for i in [0:m.size] do
      for j in [0:m[0]!.size] do
        if m[i]![j]! == '#' then
          x <- f x i j
    return x
  switchMark: Char -> Char 
  | '.' => '?'
  | '?' => '!'
  |  c  => c

  variate i j : Array (Nat × Nat × Array (Nat × Nat)) := 
    let is := #[i - 1, i, i + 1]
    let js := #[j - 1, j, j + 1]
    let forI i' := (i', j, js.map ((i', ·)))
    let forJ j' := (i, j', is.map ((·, j')))
    let arr := #[forI (i - 1), forI (i + 1), forJ (j - 1), forJ (j + 1)]
    let el (i: Fin 4) := arr[i + round]
    #[el 0, el 1, el 2, el 3]

  needGo i j: Bool :=
    [i-1, i, i+1].any (λ x => [j-1, j, j+1].any (fun y => (x != i || y != j) && m[x]![y]! == '#'))
          
  tryStep prep mf i j: IO (Matrix Char × Bool) := do
    if !(needGo i j) then return mf
    let (m', f) := mf
    for (x, y, neis) in variate i j do
      if neis.all (fun (i', j') => m[i']![j']! != '#') then 
        return if prep then
          (m'.modify x (·.modify y switchMark), true)
        else if m'[x]![y]! != '!' then
          ((m'.modify x (·.set! y '#')).modify i (·.set! j '.'), true)
        else (m', f)
    return (m', f)

def emptys (m: Matrix Char) : Nat := calcul 
where 
  calcul: Id Nat := do
    let mut (x1, y1, x2, y2) := (100000, 100000, 0, 0)
    for i in [0:m.size] do
      let r := m[i]!
      for j in [0:r.size] do
        if r[j]! == '#' then
          x1 := min x1 i
          y1 := min y1 j
          x2 := max x2 i
          y2 := max y2 j

    let mut res := 0
    for i in [x1:x2+1] do
      for j in [y1:y2+1] do
        if m[i]![j]! == '.' then
          res := res + 1
    return res  

def step (m: Matrix Char) (round: Nat := 0): IO (Matrix Char × Bool) := do
  let i := round % 4
  let m := if hasBound m then frame 1 '.' m else m
  if p: i < 4 then step' m ⟨i, p⟩ else pure (m, false)


partial def howLong (m: Matrix Char) (round: Nat := 0): IO Nat := do
  let (m, moved) <- step m round
  if moved then howLong m (round + 1) else pure round

def main: IO Unit := do
  let steps := 10
  let ls <- readLines 23
  let orig := (ls.map (·.toList.toArray)).toArray
  -- showMatrix ls
  let mut ls := orig
  for i in [0:steps] do
    (ls, _) <- step ls i
  -- showMatrix ls
  IO.println <| emptys ls
  let r <- howLong orig
  IO.println (r + 1)
