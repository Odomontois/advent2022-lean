import Advent
import Std

open Lean (HashMap HashSet)

inductive Material |ore  |obsidian |geode |clay deriving Repr, Inhabited

namespace Material

instance : ToString Material where 
  toString
  | ore => "ore"
  | obsidian => "obsidian"
  | geode => "geode"
  | clay => "clay"

def index: Material -> Fin 4 
| ore => 0
| obsidian => 1
| geode => 2
| clay => 3

def fromIndex: Fin 4 -> Material
| 0 => ore
| 1 => obsidian
| 2 => geode
| 3 => clay

theorem toFrom(m: Material): m = fromIndex (index m) := by
  cases m <;> simp [index, fromIndex]

theorem fromTo(i: Fin 4):  i = index (fromIndex i) := by
  match i with 
  | 0 => simp
  | 1 => simp
  | 2 => simp
  | 3 => simp

def values := [ore, clay, geode, obsidian]

def valArray := values.toArray

def names := values.map (s!"{·}")

def parseMat: Parse Material :=
  Parse.choose <| names.zip values


structure Map' (α: Type) where
  ore : α
  obsidian: α
  geode: α
  clay : α
deriving Ord, BEq, Hashable, Inhabited, Lean.ToJson

namespace Map' 
  def off (f: Material -> α): Map' α := ⟨f Material.ore, f Material.obsidian, f Material.geode, f Material.clay⟩
  variable (map: Map' α)


  def getMat (mat: Material): α := 
    match mat with
    | Material.ore => map.ore
    | Material.obsidian => map.obsidian
    | Material.geode => map.geode
    | Material.clay => map.clay

  
  def modifyMat (mat: Material) (f: α -> α): Map' α := 
     match mat with
    | Material.ore => {map with ore := f map.ore}
    | Material.obsidian => {map with obsidian := f map.obsidian}
    | Material.geode => {map with geode := f map.geode}
    | Material.clay => {map with clay := f map.clay}

  def setMat (mat: Material) (x: α): Map' α := 
    match mat with
    | Material.ore => {map with ore := x}
    | Material.obsidian => {map with obsidian := x}
    | Material.geode => {map with geode := x}
    | Material.clay => {map with clay := x}

  def zipWith (f: α -> β -> γ) (map': Map' β): Map' γ := 
    ⟨ f map.ore map'.ore, f map.obsidian map'.obsidian, f map.geode map'.geode, f map.clay map'.clay  ⟩

  def mapLE [LE α] [(x: α) -> (y: α) -> Decidable (x <= y)] (xs ys: Map' α): Bool := 
    (xs.ore <= ys.ore) && (xs.obsidian <= ys.obsidian) && (xs.geode <= ys.geode) && (xs.clay <= ys.clay)

  instance [LE α] [(x: α) -> (y: α) -> Decidable (x <= y)]: LE (Map' α) where
    le x y := mapLE x y

  instance [LE α] [(x: α) -> (y: α) -> Decidable (x <= y)] {xs ys: Map' α}: Decidable (xs <= ys) := 
    decidable (mapLE xs ys)
end Map'

def Map α := {arr : Array α // arr.size = 4}

namespace Map
  def mk (x: α): Map α := ⟨Array.mkArray 4 x, Eq.refl 4⟩
  def of (or g obs c: α): Map α := ⟨ Array.mkArray4 or g obs c, Eq.refl 4⟩
  def off (f: Material -> α): Map α := of (f ore) (f obsidian) (f geode) (f clay)
 
  variable (map: Map α)

  instance [Inhabited α]: Inhabited (Map α) where
    default := mk default

  instance [BEq α]: BEq (Map α) where
    beq x y := x.val == y.val

  instance [ToString α]: ToString (Map α) where
    toString map := String.join <| 
                    (["["] ++ · ++ ["]"]) <| 
                    List.intersperse ", " <| 
                    names.zipWith (s!"{·}: {.}") map.val.toList

  instance [Hashable α]: Hashable (Map α) where
    hash map := hash map.val

  instance [Lean.ToJson α]: Lean.ToJson (Map α) where
    toJson map := Lean.toJson map.val


  def getMat (mat: Material): α := 
    match map with 
    | ⟨ arr, p ⟩ => arr.get <| cast (by rw[p]) <| index mat 
  
  def modifyMat (mat: Material) (f: α -> α): Map α := 
    match map with 
    | ⟨ arr, p ⟩ => Subtype.mk (arr.modify (index mat) f) <| 
      by rw [<- Array.modify_stable_size]; assumption

  def setMat (mat: Material) (x: α): Map α := 
    match map with 
    | ⟨ arr, p ⟩ => Subtype.mk (arr.set (cast (by rw[p]) (index mat)) x) <| by simp; assumption

  def zipWith (f: α -> β -> γ) (map': Map β): Map γ := 
    match map, map' with 
    | ⟨ arr, p ⟩, ⟨ arr', p' ⟩ => ⟨ arr.zipWith arr' f,  Array.zipWith_eq_size f p p' ⟩

  def mapLE [LE α] [(x: α) -> (y: α) -> Decidable (x <= y)] (xs ys: Map α): Bool := 
    values.all (fun m => xs.getMat m <= ys.getMat m)

  instance [LE α] [(x: α) -> (y: α) -> Decidable (x <= y)]: LE (Map α) where
    le x y := mapLE x y

  instance [LE α] [(x: α) -> (y: α) -> Decidable (x <= y)] {xs ys: Map α}: Decidable (xs <= ys) := 
    decidable (mapLE xs ys)

  def mapLT [LT α] [(x: α) -> (y: α) -> Decidable (x < y)] (xs ys: Map α): Bool := 
    values.all (fun m => xs.getMat m < ys.getMat m)

  instance [LT α] [(x: α) -> (y: α) -> Decidable (x < y)]: LT (Map α) where
    lt x y := mapLT x y

  instance [LT α] [(x: α) -> (y: α) -> Decidable (x < y)] {xs ys: Map α}: Decidable (xs < ys) := 
    decidable (mapLT xs ys)
end Map



instance [ToString α] : ToString (Material -> α) where
  toString f := String.join <| (["["] ++ · ++ ["]"]) <| List.intersperse ", " <| names.zipWith (s!"{·}: {f .}") values
end Material

open Material

def Blueprint := Map' (Map' Nat) deriving ToString
namespace Blueprint

def parseBot (mat: Material): Parse (Map' Nat) := open Parse in do 
ws
str "Each "  
str s!"{mat}"
str " robot costs "
let cost := do
  let amt <- nat
  str " "
  let mat <- Material.parseMat
  return (amt, mat)    
let costs <- cost.repSep! " and "
let mut costArr := Material.Map'.mk 0 0 0 0
for (amt, mat) in costs do
  costArr := costArr.modifyMat mat (· + amt)
str "."
return costArr

def parse: Parse Blueprint := open Parse in do
  ws
  str "Blueprint "
  _ <- nat
  str ":"
  ws

  let oreBot <- parseBot ore
  let clayBot <- parseBot clay
  let obsBot <- parseBot obsidian
  let geodeBot <- parseBot geode

  return {
     ore := oreBot 
     clay := clayBot 
     geode := geodeBot 
     obsidian := obsBot
  }
end Blueprint

structure State where
  time: Nat
  robots: Map' Nat
  mats: Map' Nat
deriving BEq, Inhabited, Hashable, Lean.ToJson

abbrev Cache := HashMap State Nat

def simulate (bp: Blueprint) (time: Nat) (robots: Map' Nat) (mats: Map' Nat) : StateM Cache Nat := 
match time with 
| 0 => pure <| mats.getMat geode
| time + 1 => do
  let cache <- StateT.get
  let state: State := ⟨ time, robots, mats ⟩
  if let some res := cache.find? state
  then return res
  let mats' := robots.zipWith (· + ·) mats
  let mut res <- simulate bp time robots mats'
  for mat in Material.values do
    let reqs := bp.getMat mat
    if reqs <= mats then 
      let mats'' := mats'.zipWith (· - ·) reqs
      let robots' := robots.modifyMat mat (· + 1)
      let branch <- simulate bp time robots' mats''
      res := max res branch
  StateM.update (·.insert state res)
  return res

structure State' where
  robots: Map' Nat 
  mats: Map' Nat
deriving BEq, Hashable, Ord, Inhabited, Lean.ToJson

def stateLT (xs ys: State'): Bool := xs.robots <= ys.robots && xs.mats <= ys.mats && !(xs == ys)

instance : LT State' where
  lt x y := stateLT x y

instance {xs ys: State'}: Decidable (xs < ys) := decidable (stateLT xs ys)


def simulateOne (bp: Blueprint) (results: Array State') (state: State'): Id (Array State') := do
  let ⟨ robots, mats ⟩ := state
  let mats' := robots.zipWith (· + ·) mats
  let mut results := results.push {state with mats := mats'}
  for mat in Material.values do
    let reqs := bp.getMat mat
    if reqs <= mats then 
      let mats'' := mats'.zipWith (· - ·) reqs
      let robots' := robots.modifyMat mat (· + 1)
      results := results.push ⟨robots', mats''⟩
  results

def simulateStep (bp: Blueprint) (states: Array State'): Array State' := 
  let states' := states.foldl (simulateOne bp) Array.empty
  let states' := states'.uniques
  let groups := states'.foldl (fun hm s =>   
    hm.insert s.robots <|
    if let some xs := hm.find? s.robots
    then xs.push s.mats
    else #[s.mats]
  )  (HashMap.empty : HashMap (Map' Nat) (Array (Map' Nat)))
  let groups := groups.toArray

  states'.filter (fun st => ! (groups.any (fun (robots, mats) => 
    if robots == st.robots 
    then mats.any ( fun x => st.mats <= x && st.mats != x ) 
    else if st.robots <= robots
    then mats.any ( st.mats <= · )
    else false
  )))



open Material
def main: IO Unit := do
  let s <- readInput 19
  let bps <- Blueprint.parse.rep.runIO s
  let robots :=  ⟨1, 0, 0, 0 ⟩
  let mats := ⟨0, 0, 0, 0⟩
  let mut score := 0
  let start <- IO.monoMsNow
  -- for (i, bp) in bps.enum do
  --   let (result, c) := (simulate bp 24 robots mats).run HashMap.empty
  --   IO.println s!"blueprint {i + 1}: {bp}"
  --   IO.println result
  --   IO.println c.size
  --   score := score + (i + 1) * result
  --   let cur <- IO.monoMsNow
  --   IO.println s! "elapsed {cur - start} ms"

  for (i, bp) in bps.enum do
      IO.println s!"blueprint {i + 1}"
      let mut gen := #[⟨robots, mats⟩]
      for g in [0:24] do
        gen := simulateStep bp gen
        -- IO.println gen
        IO.println s!"generation {g} size {gen.size}"


  -- let mut score := 1

  -- for (i, bp) in bps.enum.take 3 do
  --   let (result, c) := (simulate bp 32 robots mats).run HashMap.empty
  --   IO.println s!"blueprint {i + 1}: {bp}"
  --   IO.println result
  --   IO.println c.size
  --   score := score * result

  -- IO.println s!"score is {score}"

  