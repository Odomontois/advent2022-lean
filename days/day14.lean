import Advent 

abbrev Band := List (Nat × Nat)
abbrev Map := Array (Array Char)

def band (s: String) : Band :=
  (s.splitOn " -> ").map <| fun s => 
    match (s.splitOn ",").map (·.toNat!) with
    | [x, y] => (x, y)
    | xs => panic! s!"expecting pair, got {xs}"

def ranges (x y : Nat): List Nat := 
  if x <= y 
  then (List.range (y - x)).map (x + ·)
  else (List.range (x - y)).map (x - ·)


def rocks (acc: List Band) (band: Band): Band := 
  match band with
  | (x1, y1) :: rest@((x2, y2) :: _) => 
    let gen := 
      if x1 == x2 then (ranges y1 y2).map ((x1, ·))
      else if y1 == y2 then (ranges x1 x2).map ((., y1))
      else []
    rocks (gen :: acc) rest
  | final => (final :: acc).reverse.join


def buildMap (b: Band): Nat × Map := 
  let xs := b.map (·.fst)
  let ys := b.map (·.snd)
  let xFrom := 0
  let xTo := xs.maximum?.get! * 2
  let yFrom := 0
  let yTo := ys.maximum?.get! + 1
  let arr := Array.mkArray (yTo - yFrom + 1) <| Array.mkArray (xTo - xFrom + 2) ' '
  let res := b.foldl (fun arr (x, y) => arr.modify (y - yFrom) (·.set! (x - xFrom) '#') ) arr
  let sx := 500 - xFrom
  (sx, res.modify 0 (·.set! sx '+'))

mutual 
partial def zand (x y: Nat): StateM Map Char := do
  let m <- StateT.get
  if x < 0 || y >= m.size || x >= m[0]!.size
  then return '~'
  
  let cur := m[y]![x]!
  if cur != ' ' && cur != '+' then return cur

  let mine <- zandFlow x y
  StateM.update <| (·.modify y (·.set! x mine))

  return mine


partial def zandFlow (x y: Nat): StateM Map Char := do
  let down <- zand x (y + 1)
  if down == '~' then return '~'
  let left <- zand (x - 1) (y + 1)
  if left == '~' then return '~'
  let right <- zand (x + 1) (y + 1)
  if right == '~' then return '~'
  return 'o'  
end

def showMap (m: Map): IO Unit := do
  for l in m do
    IO.println <| String.mk <| l.toList

def sandCount(m: Map) := m.foldl (· + ·.foldl (· + if · == 'o' then 1 else 0) 0) 0


def main : IO Unit := do
  let lines <- readLines 14
  let bands := lines.map band
  let rs := bands.bind (rocks [])
  let (sx, map) := buildMap rs
  let (_, res) := zand sx 0 map

  IO.println <| sandCount res

  let floorMap := map.push (Array.mkArray map[0]!.size '#')
  let (_, floorRes) := zand sx 0 floorMap
  -- showMap floorRes

  IO.println <| sandCount floorRes




