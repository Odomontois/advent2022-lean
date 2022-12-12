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

theorem emptyPull (q: QueueData α): q.toList = [] <-> q.pull = none := by
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

def toList (q: Queue α): List α := 
  q.lift (·.toList) <| by intros; assumption

def send (q: Queue α) (x: α): Queue α := 
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
    
syntax "qsound" : tactic

macro_rules
  | `(tactic| qsound) => `(tactic| apply Quot.sound; simp [QueueSetoid, QueueData.rel, QueueData.toList])


def pull (q: Queue α) : Option (α × Queue α) :=
  q.lift (fun qd => qd.pull.map (fun (a, xs) => (a, Quot.mk _ xs))) <| by
  simp [HasEquiv.Equiv]
  unfold Setoid.r
  intros a b p
  cases a; case mk ia ta =>
  cases b; case mk ib tb => 
  simp [QueueSetoid, QueueData.rel, QueueData.toList] at p
  cases ia
  let p1 := congrArg List.reverse p
  . cases ta
    . simp at p
      cases ib
      . cases tb
        . simp
        . simp at p1         
      . contradiction
    . case cons iah iat =>
      cases ib
      . cases tb
        . simp at p1
        . case cons tbh tbt =>
          simp at p1
          rw [p1.left, p1.right] 
      . case cons ibh ibt => 
        simp [Option.map, QueueData.pull]
        simp at p
        generalize List.reverse iat = riat at p
        cases riat
        . simp at p
          simp
          rw [p.left]
          simp
          let p2 := List.append_eq_nil p.right
          let p3 := congrArg List.reverse p2.right
          simp at p3
          rw [← p2.left, ← p3]
        . case cons hriat triat =>
          simp at p
          rw [p.left] 
          simp
          rw [p.right]
          qsound
  . case cons iah iat => 
    cases ib
    . simp at p
      simp [Option.map, QueueData.pull]
      generalize List.reverse tb = rtb at p
      cases rtb
      . simp at p
      . case cons hrtb trtb => 
        simp at p
        rw [p.left]
        simp
        qsound
        exact p.right
    . case cons ibh ibt =>
      simp at p
      rw [p.left]
      simp [Option.map, QueueData.pull]
      qsound
      exact p.right

def isEmpty (q: Queue α): Bool := 
  q.lift (·.isEmpty) <| by admit


instance: Inhabited (Queue α) where
  default := Quot.mk _ ⟨[], []⟩


end Queue