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

abbrev IsSingle(p: Packet) := ∃ n, p = Single n

theorem multNotSingle (xs): ¬ IsSingle (Multiple xs) := by
  intros ex
  cases ex
  contradiction

def isSingle?: (p: Packet) -> Decidable p.IsSingle
| Single n => Decidable.isTrue (Exists.intro n (Eq.refl _))
| Multiple xs => Decidable.isFalse <| multNotSingle xs

mutual 
def level: Packet -> Nat 
| Single _ => 0
| Multiple xs => levels xs + 2


def levels: List Packet -> Nat
| [] => 0
| x :: xs => x.level + (levels xs) + 1
end

theorem children_mult_levels {x : Packet} {ys : List Packet}: levels (children x) + levels ys < x.level + (Multiple ys).level := by 
  cases x <;> simp [children, levels, level]
  . case Single x => 
    rw [Nat.add_comm]
    apply Nat.lt_succ_self
  . case Multiple xs => 
    conv => 
      rhs
      rw [Nat.add_assoc]
      conv => 
        rhs
        rw [← Nat.add_assoc]
        conv => 
          lhs
          rw [Nat.add_comm]  
        rw [Nat.add_assoc]
        simp [Nat.add]
      rw [←Nat.add_assoc]
    apply @Nat.add_lt_add_left 0
    apply Nat.zero_lt_succ

theorem children_levels {x y : Packet} (p: ¬ (x.IsSingle ∧ y.IsSingle)) : levels x.children + levels y.children < x.level + y.level := by
  cases x 
  . case Single x =>
    cases y
    . case Single y =>
      apply False.elim
      apply p
      constructor
      . exists x
      . exists y
    . case Multiple ys => 
      apply children_mult_levels
  . case Multiple xs =>
      conv => 
        lhs
        rw [Nat.add_comm] 
      conv => 
        rhs
        rw [Nat.add_comm] 
      apply children_mult_levels


  
private theorem sum_lt (x y: Nat): x < x + y + 1 := by 
  rw [Nat.add_assoc]
  apply @Nat.add_lt_add_left 0
  apply Nat.zero_lt_succ

private theorem sum_lt' (x y: Nat): x < y + x + 1 := by 
  rw [Nat.add_comm y x]
  apply sum_lt


mutual
  def comparePacket (xp yp : Packet): Ordering  :=
  match xp.isSingle? &&& yp.isSingle? with
  | isTrue p => 
    match xp, yp with
    | Single x, Single y => compare x y 
    | Multiple xs , _ => absurd p.left <| multNotSingle xs 
    | _, Multiple ys => absurd p.right <| multNotSingle ys
  | isFalse p => 
    have := children_levels p
    let _ := Nat.lt
    comparePackets xp.children yp.children

  def comparePackets: List Packet -> List Packet -> Ordering 
  | x :: xs, y :: ys => 
    have: level x + level y < levels (x :: xs) + levels (y :: ys) := by 
      apply Nat.add_lt_add <;> simp [levels] <;> apply sum_lt
    have: levels xs + levels ys < levels (x :: xs) + levels (y :: ys) := by 
      apply Nat.add_lt_add <;> simp [levels] <;> apply sum_lt'
    match comparePacket x y with 
    | Ordering.eq => comparePackets xs ys
    | other => other
  | [], [] => Ordering.eq  
  | _ :: _, [] => Ordering.gt
  | [], _ :: _ => Ordering.lt
end 
termination_by 
  comparePacket x y => x.level + y.level
  comparePackets xs ys => levels xs + levels ys

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
  