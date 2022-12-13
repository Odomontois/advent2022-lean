import Advent
import Lean

open Lean.FromJson
open Lean (Json)

inductive Packet where
| Single: Nat -> Packet
| Multiple: List Packet -> Packet
deriving Lean.ToJson, Inhabited

namespace Packet

def separators : List Packet := 
let wrap := Multiple ∘ ([·]) ∘ Multiple ∘ ([·]) ∘ Single
[wrap 2, wrap 6]

def children : Packet -> List Packet
| Single x => [Single x]
| Multiple xs => xs

mutual
  partial def comparePacket: Packet -> Packet -> Ordering
  | Single x, Single y => compare x y 
  | xp, yp => comparePackets xp.children yp.children

  partial def comparePackets: List Packet -> List Packet -> Ordering 
  | x :: xs, y :: ys => match comparePacket x y with 
    | Ordering.eq => comparePackets xs ys
    | other => other
  | [], [] => Ordering.eq  
  | _ :: _, [] => Ordering.gt
  | [], _ :: _ => Ordering.lt
end 

instance : Ord Packet where
  compare := comparePacket

instance : BEq Packet where
  beq := (compare · · == Ordering.eq)

instance : LE Packet := leOfOrd
 
partial def fromJsonImpl(j: Json): Except String Packet := do
  try 
    let x <- fromJson? j
    return Single x
  catch _ => 
    let list : List Json <- fromJson? j
    let packets <- list.mapM fromJsonImpl
    return Multiple packets
  
instance : Lean.FromJson Packet where
  fromJson? := fromJsonImpl

end Packet

def decode [Lean.FromJson α] (s: String): Except String α := do
  let json <- Json.parse s
  fromJson? json

def parseIO (s: String): IO Packet := 
  match decode s with 
  | Except.ok x => pure x
  | Except.error s => throw <| IO.userError s
 
def compareBlock: List Packet -> Bool
| [x, y] => x <= y
| b => panic! s!"bad block {b}"


def main : IO Unit := do
  let blocks <- readBlocks 13
  let parsedBlocks <- blocks.mapM (·.mapM parseIO)
  let mut x : Nat := 0
  for (i, b) in parsedBlocks.enum do
    let bb := compareBlock b
    IO.println (i + 1, bb)
    if bb then 
      x := x + i + 1
  IO.println x

  let allPackets := Packet.separators.toArray ++ parsedBlocks.join.toArray
  let sortedPackets := allPackets.qsort (· <= ·)
  let sepIndex := Packet.separators 
                  |> List.filterMap (sortedPackets.indexOf? ·) 
                  |> List.map (·.val + 1)
  IO.println sepIndex
  IO.println sepIndex.product
  