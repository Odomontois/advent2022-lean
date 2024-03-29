import Lean
import MathLib


inductive Side where 
 | left 
 | right 
deriving BEq, Repr, Inhabited

inductive Pass (α: Type)
| one : α -> Pass α
| driver
deriving BEq, Repr, Inhabited


def U := Array
open Pass

abbrev Bank P := List (Pass P)

def State P := Bank P × Bank P

instance : Inhabited (State P) where default := ([], [])

class Moves (P : Type) where
  allowed: State P -> Bool

class ForbiddenMoves (P: Type) where
  forbidden: List (P × P)

def checkBank [BEq P] [FM: ForbiddenMoves P] (b: Bank P): Bool := 
  not <| FM.forbidden.any <| λ (x, y) => b.contains (one x) && b.contains (one y) && !b.contains driver

instance [BEq P] [ForbiddenMoves P]: Moves P where
  allowed |(l, r) => checkBank l && checkBank r && 
    (l.filter (· == driver) ++ r.filter (· == driver)).length == 1

def State.good [m: Moves P] := m.allowed

def side [BEq α] (sides: List α × List α) (el: α): Option Side := 
  if sides.fst.contains el then some .left
  else if sides.snd.contains el then some .right
  else none

def move [BEq P] [Moves P] (s : State P) (pass: Pass P): Option (State P) := 
  do
    let driverSide <- side s driver
    let passengerSide <- side s pass
    if driverSide != passengerSide then none 
    let crossing := if pass == driver then [driver] else [driver, pass]
    let res := match driverSide with
    | .left => (s.fst.removeAll crossing, s.snd.append crossing)
    | .right => (s.fst.append crossing, s.snd.removeAll crossing)
    if !res.good then none else return res

def Option.extract (o: Option α) (_e: o.isSome): α :=
 match _eo: o with
 | some x => x
 | none => by contradiction

def equalBanks  [BEq P] (b₁ b₂ : Bank P): Bool := 
  b₁.removeAll b₂ == [] && b₂.removeAll b₁ == []

def equalStates [BEq P] (s₁ s₂ : State P): Bool := 
  equalBanks s₁.fst s₂.fst && equalBanks s₁.snd s₂.snd

inductive Chain [BEq P] [Moves P] : State P -> State P -> Type where
  | done {s t : State P} (goodStart: s.good) (e: equalStates s t) : Chain s t
  | step (p: Pass P) (correct: (move s p).isSome) (next: Chain ((move s p).extract correct) u): Chain s u
  
inductive WGC where
  | wolf
  | goat
  | cabbage
deriving BEq, Repr, Inhabited

instance : ForbiddenMoves WGC where
  forbidden := [(.goat, .cabbage), (.wolf, .goat)]

def all: Bank WGC := [driver, one .goat, one .wolf, one .cabbage]
def onlyGoat: Bank WGC := [driver, one .goat]

def solution0: Chain (all, []) (all, []) := .done (by simp) (by simp)

syntax "drive" term: tactic
macro_rules
|`(tactic| drive $e) => 
  `(tactic| apply (Chain.step $e (by simp)); conv =>  lhs; reduce)

macro "chill" : tactic => `(tactic | exact (Chain.done (by simp) (by simp)))

def solution1: Chain (onlyGoat, []) ([], onlyGoat) := by
  drive one .goat
  chill

abbrev alone: Pass α := driver

open WGC

def solution2: Chain (all, []) ([], all) := by
  unfold all
  drive one goat
  drive alone
  drive one cabbage
  drive one goat
  drive one wolf
  drive alone
  drive one goat
  chill

def stupidState: State WGC := ([driver, driver], [driver, driver])

def stupidSolution: Chain stupidState stupidState := by admit
  
    
  