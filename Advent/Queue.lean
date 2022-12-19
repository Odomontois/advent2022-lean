import Lean
import Advent.List

class QueueData (α : Type u) where
  init: List α 
  tail: List α

namespace QueueData
def toList (q: QueueData α): List α := q.init ++ q.tail.reverse

def send (q: QueueData α) (a: α): QueueData α := {q with tail := a :: q.tail}

def pull (q: QueueData α) : Option (α × QueueData α) :=
  match q.init with
  | x :: xs  => some (x, ⟨xs, tail⟩)
  | [] => match q.tail.reverse with 
    | x :: xs => some (x, ⟨xs, []⟩)
    | []      => none

def isEmpty (q: QueueData α) : Bool := 
  q.init.isEmpty && q.tail.isEmpty


def rel (a b : QueueData α): Prop := a.toList = b.toList

theorem nonEmptyAppend {xs ys: List α} {x: α} (p: xs ++ (x :: ys) = []) : False := 
  by cases xs <;> simp at p

theorem isEmptyToList (q: QueueData α): q.isEmpty <-> q.toList = [] := by
  simp [isEmpty, toList, List.isEmpty]
  cases q.init <;> cases q.tail <;> simp
  case cons h t => 
  simp
  intro p
  apply nonEmptyAppend p

theorem emptyPull {q: QueueData α}: q.toList = [] <-> q.pull = none := by
  simp [toList, pull]
  cases q.init <;> cases q.tail <;> simp
  case cons h t => 
  constructor
  generalize t.reverse = rt
  . intro q
    let u := nonEmptyAppend q
    contradiction
  . generalize up: List.reverse t ++ [h] = u
    intro q
    cases u <;> simp at q <;> simp

theorem nonEmptyPull {q: QueueData α} {x : α} {xs: List α}: 
  q.toList = x :: xs  <-> (exists (qt: QueueData α), qt.toList = xs ∧ q.pull = some (x, qt)) := by
  simp [toList, pull]
  cases q.init 
  generalize p : q.tail.reverse = tr
  . cases tr <;> simp
    . intro e
      cases e
      assumption
    . case cons h t => 
      constructor
      . intro p1 
        exists ⟨ t , []⟩
        simp [*]
      . intro qe
        cases qe with | intro qt p1 => 
        cases qt with | mk qi qt =>
        simp [*]
        let p2 := p1.right.right
        simp at p1
        let p3 := congrArg (·.init) p2
        let p4 := congrArg (·.tail) p2
        simp at p3 p4
        rw [← p3, ← p4] at p1
        simp at p1
        simp [p1]

  . case cons h t => 
    simp
    constructor
    . intro pp
      let qt: QueueData α := ⟨ t, q.tail ⟩
      exists qt
      simp
      rw [pp.left, pp.right]    
      simp
    . intro qe
      cases qe with | intro qt pp =>  
      cases pp with | intro p1 p2 =>
      cases p2 with | intro p2 p3 => 
      cases qt with | mk qti qtt => 
      rw [p2, ← p1]
      simp
      let p4 := congrArg (·.init) p3
      let p5 := congrArg (·.tail) p3
      simp at p4 p5
      rw [p4, p5]

end QueueData

def QueueSetoid (α : Type u): Setoid (QueueData α) := {
  r := QueueData.rel
  iseqv := {
    refl := by simp [QueueData.rel]
    symm := by intros _ _ p; simp [QueueData.rel]; rw [p]
    trans := by intros _ _ _ p q; simp [QueueData.rel]; rw [p, q] 
  }
}




def Queue (α : Type u) := Quotient (QueueSetoid α) 

namespace Queue

variable (q: Queue α)

def toList: List α := 
  q.lift (·.toList) <| by intros; assumption

def send (x: α): Queue α := 
  q.lift (fun qd => Quot.mk _ (qd.send x)) <| by
    simp [HasEquiv.Equiv]
    unfold Setoid.r
    intros a b p
    cases a; case mk ia ta =>
    cases b; case mk ib tb => 
    simp [QueueData.send]
    apply Quot.sound
    simp [QueueSetoid, QueueData.rel, QueueData.toList]
    repeat rw [← List.append_assoc]
    simp [QueueSetoid, QueueData.rel, QueueData.toList] at p
    rw [p]
    
def pull: Option (α × Queue α) :=
  q.lift (fun qd => qd.pull.map (fun (a, xs) => (a, Quot.mk _ xs))) <| by
  intros a b p
  simp 
  generalize p1: a.isEmpty = aempty
  cases aempty
  . generalize p2 : a.toList = al 
    cases al
    . rw [← QueueData.isEmptyToList, p1] at p2
      contradiction
    . case cons h t => 
      let p3 := p2
      rw [QueueData.nonEmptyPull] at p3
      rw [p, QueueData.nonEmptyPull] at p2
      cases p3 with | intro bqa p5 =>
      cases p2 with | intro bqt p6 =>
      simp [p5, p6, Option.map]
      apply Quot.sound
      simp [QueueSetoid, QueueData.rel]
      rw [p5.left, p6.left]
  . rw [QueueData.isEmptyToList] at p1
    let p2 := p1
    rw [QueueData.emptyPull] at p2
    rw [p, QueueData.emptyPull] at p1
    rw [p1, p2]

def isEmpty: Bool := 
  q.lift (·.isEmpty) <| by
  intros a b p
  simp
  generalize pe: a.isEmpty = ae
  cases ae
  . generalize pl: a.toList = al
    cases al
    . rewrite [←QueueData.isEmptyToList] at pl
      rw [pe] at pl
      contradiction
    . rw [p] at pl
      generalize pe2: b.isEmpty = be
      cases be <;> simp
      rw [QueueData.isEmptyToList, pl] at pe2
      contradiction
  . rw [QueueData.isEmptyToList, p, ←QueueData.isEmptyToList] at pe
    rw [pe]

def empty: Queue α :=   Quot.mk _ ⟨[], []⟩

def peak: Option α := q.pull.map (·.fst)

def tail: Queue α := (q.pull.map (·.snd) ).getD empty

def sendMany [ForIn Id ρ α](xs: ρ) : Id (Queue α) := do
  let mut q := q
  for x in xs do
    q := q.send x
  return q

instance: Inhabited (Queue α) where
  default := empty

instance [ToString α]: ToString (Queue α) where
  toString q := "Queue" ++ q.toList.toString   

instance [Lean.ToJson α]: Lean.ToJson (Queue α) where
  toJson q := Lean.ToJson.toJson q.toList

instance : ForIn m (Queue α) α where
  forIn q b f := q.toList.forIn b f

instance [BEq α] : BEq (Queue α) where
  beq xs ys := xs.toList == ys.toList

end Queue