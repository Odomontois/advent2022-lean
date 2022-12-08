import Lean.Data.HashMap
import Advent.Read
-- import Lean.Elab.Deriving
import Lean

open Lean (ToJson HashMap)

structure Info where
  cur: Array String
  children: HashMap (Array String) (Array String)
  sizes: HashMap (Array String) Nat

instance : ToString Info where
  toString (i: Info ) := 
  s!"cur={i.cur} children={i.children.toArray} sizes={i.sizes.toArray}"

namespace Info 
  def setCur (f: Array String -> Array String) (info: Info): Info :=
    {info with cur := f info.cur}

  def addChild(name: String) (info: Info) : Info := 
  let children := (info.children.findD info.cur Array.empty).push name
  {info with children := info.children.insert info.cur children}

  def setSize (name: String) (size: Nat) (info: Info): Info := 
    let full := info.cur.push name
    {info with sizes := info.sizes.insert full size}

  def initial: Info := 
    {cur := Array.empty, children := HashMap.empty, sizes := HashMap.empty}
end Info
  

inductive Command
  | cdRoot
  | cdUp 
  | cdDown (s: String)
  | ls
  | dir (name: String)
  | file (size: Nat) (name: String)
deriving ToJson

open Command
def parse(s: String) : Option Command := 
  match s.splitOn with
  | ["$", "cd", "/"] => cdRoot
  | ["$", "cd", ".."] => cdUp
  | ["$", "cd", name] => cdDown name
  | ["$", "ls"] => ls
  | ["dir", name] => dir name
  | [size, name] => size.toNat?.map (file · name)
  | _ => none

def handleCommand(info: Info): Command ->  Info
| cdRoot => info.setCur (fun _ => Array.empty)
| cdUp => info.setCur (·.pop)
| cdDown name => info.setCur (·.push name)
| dir name => info.addChild name
| ls => info
| file size name => info |> Info.addChild name |> Info.setSize name size  

partial def calcSize (info: Info) (name: Array String): IO (Nat × Array Nat) := 
  match info.sizes.find? name with
  | some x => pure (x, Array.empty)
  | none => do
    let children := (info.children.findD name Array.empty).map name.push
    let results <- children.mapM (calcSize info)
    let mySize := results.foldl (· + ·.fst) 0
    let sizes := results.concatMap (·.snd) |> (·.push mySize)
    pure (mySize, sizes)



def main: IO Unit := do
  let inp <- readLines 7
  let cmds := inp.filterMap parse
  let res := cmds.foldl handleCommand Info.initial
  let (total, allSizes) <- calcSize res Array.empty
  let ss := allSizes 
            |> Array.filter (· < 100000) 
            |> Array.foldl (· + ·) 0
  IO.println allSizes
  IO.println ss
  let need := total - 40000000
  IO.println need
  let found := allSizes 
              |> Array.filter (· >= need)
              |> Array.foldl Min.min total
  IO.println found 

