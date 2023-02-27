import Lean
-- import Mathlib

inductive Passenger where
  | goat
  | fox
  | cabbage
deriving BEq, Repr, Inhabited

inductive Side where 
 | left 
 | right 
deriving BEq, Repr, Inhabited

-- We will encode the farmer (the captain) as the default inhabitant, i.e. none
-- So the passenger list is a List of Options

abbrev Bank P := List (Option P)
def State P := Bank P × Bank P

instance : Inhabited (State P) where default := ([], [])

class Moves (P : Type) where
  allowed: State P -> Bool

class ForbiddenMoves (P: Type) where
  forbidden: List (P × P)

@[simp] def checkBank [BEq P] [FM: ForbiddenMoves P] (b: Bank P): Bool := 
  not <| FM.forbidden.any <| λ (x, y) => b.contains x && b.contains y

instance [BEq P] [ForbiddenMoves P]: Moves P where
  allowed |(l, r) => checkBank l && checkBank r

instance : ForbiddenMoves Passenger where
  forbidden := [(.goat, .cabbage), (.fox, .goat)]

def State.good [m: Moves P] := m.allowed

def side [BEq α] (sides: List α × List α) (el: α): Option Side := 
  if sides.fst.contains el then some .left
  else if sides.snd.contains el then some .right
  else none

def move [BEq P] [Moves P] (s : State P) (pass: Option P): Option (State P) := 
  do
    let farmerSide <- side s none
    let passengerSide <- side s <| pass
    if farmerSide != passengerSide then none 
    let crossing := if pass.isSome then [none, pass] else [none]
    let res := match farmerSide with
    | .left => (s.fst.removeAll crossing, s.snd.append crossing)
    | .right => (s.fst.append crossing, s.fst.removeAll crossing)
    if !res.good then none else return res

def Option.extract (o: Option α) (_e: o.isSome): α :=
 match _eo: o with
 | some x => x
 | none => by contradiction



inductive Chain [BEq P] [Moves P] : State P -> State P -> Type where
  | done: Chain s s
  | step (p: Option P) (correct: (move s p).isSome) (next: Chain ((move s p).extract correct) u): Chain s u


def all: Bank Passenger := [none, some .goat, some .fox, some .cabbage]
abbrev goat: Bank Passenger := [none, some .goat]

def solution0: Chain (all, []) (all, []) := .done

-- #eval (move (goat, []) (some Passenger.goat))

def solution1: Chain (goat, []) ([], goat) := 
  .step (some .goat) (by simp) _
  -- apply (Chain.step (some Passenger.goat) (by simp))
  -- conv => 
  --   lhs
  --   reduce
  
    
  