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


structure Map (α: Type) where
  ore : α
  obsidian: α
  geode: α
  clay : α
deriving Ord, BEq, Hashable, Inhabited, Lean.ToJson

namespace Map 
  def off (f: Material -> α): Map α := ⟨f Material.ore, f Material.obsidian, f Material.geode, f Material.clay⟩
  variable (map: Map α)


  def getMat (mat: Material): α := 
    match mat with
    | Material.ore => map.ore
    | Material.obsidian => map.obsidian
    | Material.geode => map.geode
    | Material.clay => map.clay
    
  def modifyMat (mat: Material) (f: α -> α): Map α := 
     match mat with
    | Material.ore => {map with ore := f map.ore}
    | Material.obsidian => {map with obsidian := f map.obsidian}
    | Material.geode => {map with geode := f map.geode}
    | Material.clay => {map with clay := f map.clay}

  def setMat (mat: Material) (x: α): Map α := 
    match mat with
    | Material.ore => {map with ore := x}
    | Material.obsidian => {map with obsidian := x}
    | Material.geode => {map with geode := x}
    | Material.clay => {map with clay := x}

  def zipWith (f: α -> β -> γ) (map': Map β): Map γ := 
    ⟨ f map.ore map'.ore, f map.obsidian map'.obsidian, f map.geode map'.geode, f map.clay map'.clay  ⟩

  def sum [Add α]: α := map.ore + map.obsidian + map.geode + map.clay

  def mapLE [LE α] [(x: α) -> (y: α) -> Decidable (x <= y)] (xs ys: Map α): Bool := 
    (xs.ore <= ys.ore) && (xs.obsidian <= ys.obsidian) && (xs.geode <= ys.geode) && (xs.clay <= ys.clay)

  instance [LE α] [(x: α) -> (y: α) -> Decidable (x <= y)]: LE (Map α) where
    le x y := mapLE x y

  instance [LE α] [(x: α) -> (y: α) -> Decidable (x <= y)] {xs ys: Map α}: Decidable (xs <= ys) := 
    decidable (mapLE xs ys)

  instance [HAdd α β γ] : HAdd (Map α) (Map β) (Map γ) where
    hAdd xs ys := xs.zipWith (· + ·) ys

  instance [HSub α β γ] : HSub (Map α) (Map β) (Map γ) where
    hSub xs ys := xs.zipWith (· - ·) ys
end Map



instance [ToString α] : ToString (Material -> α) where
  toString f := String.join <| (["["] ++ · ++ ["]"]) <| List.intersperse ", " <| names.zipWith (s!"{·}: {f .}") values
end Material

open Material

def Blueprint := Map (Map Nat) deriving ToString, Inhabited
namespace Blueprint

def parseBot (mat: Material): Parse (Map Nat) := open Parse in do 
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
let mut costArr := Material.Map.mk 0 0 0 0
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
  robots: Map Nat
  mats: Map Nat
deriving BEq, Inhabited, Hashable, Lean.ToJson

abbrev Cache := HashSet State

def simulate (bp: Blueprint) (time: Nat) (robots: Map Nat) (mats: Map Nat) : StateM Cache Nat := 
match time with 
| 0 => pure <| mats.getMat geode
| time + 1 => do
  let cache <- StateT.get
  let state: State := ⟨ time, robots, mats ⟩
  if cache.contains state then return 0
  let mats' := robots + mats
  let mut res <- simulate bp time robots mats'
  for mat in Material.values do
    let reqs := bp.getMat mat
    if reqs <= mats then 
      let mats'' := mats' - reqs
      let robots' := robots.modifyMat mat (· + 1)
      let branch <- simulate bp time robots' mats''
      res := max res branch
  StateM.update (·.insert state)
  return res

-- simplified \ specialized blueprint for p2
structure SBlueprint where
  ore'ore : Nat
  clay'ore: Nat
  obs'ore: Nat
  obs'clay: Nat
  geo'ore: Nat
  geo'obs: Nat

instance: Coe Blueprint SBlueprint where
  coe bp := {
    ore'ore := bp.ore.ore
    clay'ore := bp.clay.ore
    obs'ore := bp.obsidian.ore
    obs'clay := bp.obsidian.clay
    geo'ore := bp.geode.ore
    geo'obs := bp.geode.obsidian
  }



structure SStrategy where
  ores: Nat
  clays: Nat
  clays2: Nat
  obs: Nat
deriving Lean.ToJson, Repr, BEq

def allStrategies(max: Nat): Id (Array SStrategy) := do
  let mut res := Array.empty
  for ores in [1:max + 1] do
    for clays in [1:max + 1] do
      for clays2 in [clays:max + 1] do
        for obs in [0:max + 1] do
          res := res.push <| ⟨ ores, clays , clays2, obs⟩
  return res

abbrev Robots := Map Nat
abbrev Materials := Map Nat

def runStrategy (b: SBlueprint) (s: SStrategy) (time: Nat): Id Nat := do
  let mut robots := ⟨1, 0, 0, 0⟩
  let mut mats := ⟨0, 0, 0, 0⟩
  for m in [0:time] do
    (robots, mats) := go robots mats
    -- IO.println s!"minute {m + 1} robots = {robots} mats = {mats}"
  return mats.geode
where
  buyGeodeBot? (mats: Materials) : Option Materials := 
    if b.geo'ore <= mats.ore && b.geo'obs <= mats.obsidian 
    then some {mats with ore := mats.ore - b.geo'ore, obsidian := mats.obsidian - b.geo'obs} 
    else none
  
  buyObsidianBot? (mats: Materials) (obsRobots : Nat): Option Materials := 
    if b.obs'ore <= mats.ore && b.obs'clay <= mats.clay && obsRobots <= s.obs
    then some {mats with ore := mats.ore - b.obs'ore, clay := mats.clay - b.obs'clay} 
    else none

    -- if mats.
  go (robots: Robots) (mats: Materials): (Robots × Materials) :=
    if robots.ore < s.ores && b.ore'ore <= mats.ore then
      ({robots with ore := robots.ore + 1 } ,{mats with ore := mats.ore - b.ore'ore} + robots)
    else if robots.ore == s.ores && robots.clay < s.clays && b.clay'ore <= mats.ore then
      ({robots with clay := robots.clay + 1}, {mats with ore := mats.ore - b.clay'ore} + robots)
    else if let some mats := buyObsidianBot? mats robots.obsidian then
      ({robots with obsidian := robots.obsidian + 1}, (mats + robots))
    else if let some mats := buyGeodeBot? mats then 
      ({robots with geode := robots.geode + 1}, (mats + robots))
    else if let some mats := buyObsidianBot? mats 0 then
      ({robots with obsidian := robots.obsidian + 1}, (mats + robots))
    else if robots.ore == s.ores && robots.clay < s.clays2 && b.clay'ore <= mats.ore then
      ({robots with clay := robots.clay + 1}, {mats with ore := mats.ore - b.clay'ore} + robots)
    else (robots, (mats + robots))
      
def bestStrategy (b: SBlueprint) (time: Nat) (top := 10): Id Nat := do
  let mut best := 0
  let all <- allStrategies top
  for s in all do 
    let res <- runStrategy b s time
    best := max best res
  return best 

def ssimulate (bp: SBlueprint) (time: Nat): StateM Cache Nat := do
  go 0 ⟨1, 0, 0, 0⟩ ⟨0, 0, 0, 0⟩ time
where 
  -- bootstrap bots ore
  -- | 0, _ => pure 0
  -- | time, 0 => go ⟨bots, 0, 0, 0⟩ ⟨ore, 0, 0, 0⟩ time
  -- | time + 1, breq + 1 =>
  --   if bp.ore'ore <= ore
  --   then bootstrap (bots + 1) (ore + bots - bp.ore'ore) time breq
  --   else bootstrap bots (ore + bots) time (breq + 1)

  oreLimit := 4
  clayLimit := 19
  obsidianLimit := 17 

  go (phase : UInt8) (robots: Robots) (mats: Materials)
  | 0 => pure mats.geode
  | time + 1 => do
    let cache <- StateT.get
    let state: State := ⟨ time, robots, mats ⟩
    if cache.contains state then return 0
    StateT.set <| cache.insert state
    let mats' := robots + mats
    let mut res := 0
    if bp.geo'ore <= mats.ore && bp.geo'obs <= mats.obsidian then
      res <- go 2
            {robots with geode := robots.geode + 1} 
            {mats' with ore := mats'.ore - bp.geo'ore, obsidian := mats'.obsidian - bp.geo'obs } 
            time
    else     
      if bp.ore'ore <= mats.ore && robots.ore < oreLimit && phase == 0 then
        res <- go phase
                  {robots with ore := robots.ore + 1} 
                  {mats' with ore := mats'.ore - bp.ore'ore } 
                  time
      if bp.clay'ore <= mats.ore && robots.clay < clayLimit  && phase < 2 then
        let next <- go phase
                  {robots with clay := robots.clay + 1} 
                  {mats' with ore := mats'.ore - bp.clay'ore } 
                  time
        res := max res next
      if bp.obs'ore <= mats.ore && bp.obs'clay <= mats.clay && robots.obsidian < obsidianLimit then
        let next <- go  (max 1 phase)
                        {robots with obsidian := robots.obsidian + 1}
                        {mats' with ore := mats'.ore - bp.obs'ore, clay := mats'.clay - bp.obs'clay}
                        time
        res := max res next

      let next <- go phase robots mats' time
      res := max res next

    return res
open Material


def main: IO Unit := do
  let s <- readInput 19
  let bps <- Blueprint.parse.rep.runIO s

  let mut score := 1
  for (i, bp) in bps.enum.take 3 do
    let res: Nat := bestStrategy bp 32
    IO.println s!"blueprint {i + 1} {res}" 
    score := score * res
  IO.println s!"score = {score}"
  -- IO.println (allStrategies 2)
  -- score := 0
  -- for (i, bp) in bps.enum do
  --   let res : Nat := bestStrategy bp 24 20
  --   IO.println s!"blueprint {i + 1}: {res}"
  --   score := score + (i + 1) * res
  -- IO.println score




  -- let robots: Map Nat :=  ⟨1, 0, 0, 0⟩
  -- let mats: Map Nat := ⟨0, 0, 0, 0⟩
  score := 1
  for (i, bp) in bps.enum.take 3 do
    let result: Nat := (ssimulate bp 32).run' HashSet.empty
    IO.println s!"(slow) blueprint {i + 1}: {bp}"
    IO.println result
    -- IO.println c.size
    score := score * result

  IO.println s!"score is {score}"

def Map'  α := {arr : Array α // arr.size = 4}

namespace Map' 
  def mk (x: α): Map'  α := ⟨Array.mkArray 4 x, Eq.refl 4⟩
  def of (or g obs c: α): Map'  α := ⟨ Array.mkArray4 or g obs c, Eq.refl 4⟩
  def off (f: Material -> α): Map'  α := of (f ore) (f obsidian) (f geode) (f clay)
 
  variable (map: Map'  α)

  instance [Inhabited α]: Inhabited (Map'  α) where
    default := mk default

  instance [BEq α]: BEq (Map'  α) where
    beq x y := x.val == y.val

  instance [ToString α]: ToString (Map'  α) where
    toString map := String.join <| 
                    (["["] ++ · ++ ["]"]) <| 
                    List.intersperse ", " <| 
                    names.zipWith (s!"{·}: {.}") map.val.toList

  instance [Hashable α]: Hashable (Map'  α) where
    hash map := hash map.val

  instance [Lean.ToJson α]: Lean.ToJson (Map'  α) where
    toJson map := Lean.toJson map.val


  def getMat (mat: Material): α := 
    match map with 
    | ⟨ arr, p ⟩ => arr.get <| cast (by rw[p]) <| index mat 
  
  def modifyMat (mat: Material) (f: α -> α): Map'  α := 
    match map with 
    | ⟨ arr, p ⟩ => Subtype.mk (arr.modify (index mat) f) <| 
      by rw [<- Array.modify_stable_size]; assumption

  def setMat (mat: Material) (x: α): Map'  α := 
    match map with 
    | ⟨ arr, p ⟩ => Subtype.mk (arr.set (cast (by rw[p]) (index mat)) x) <| by simp; assumption

  def zipWith (f: α -> β -> γ) (map': Map'  β): Map'  γ := 
    match map, map' with 
    | ⟨ arr, p ⟩, ⟨ arr', p' ⟩ => ⟨ arr.zipWith arr' f,  Array.zipWith_eq_size f p p' ⟩

  def mapLE [LE α] [(x: α) -> (y: α) -> Decidable (x <= y)] (xs ys: Map'  α): Bool := 
    values.all (fun m => xs.getMat m <= ys.getMat m)

  instance [LE α] [(x: α) -> (y: α) -> Decidable (x <= y)]: LE (Map'  α) where
    le x y := mapLE x y

  instance [LE α] [(x: α) -> (y: α) -> Decidable (x <= y)] {xs ys: Map' α}: Decidable (xs <= ys) := 
    decidable (mapLE xs ys)
end Map' 

