import Lean
import Advent.List

class QueueData (α : Type u) where
  init: List α 
  tail: List α

def QueueData.toList (q: QueueData α): List α := q.init ++ q.tail.reverse

def QueueData.send (q: QueueData α) (a: α): QueueData α := {q with tail := a :: q.tail}

def QueueData.pull (q: QueueData α) : Option (α × QueueData α) :=
  match q.init with
  | x :: xs  => some (x, ⟨xs, tail⟩)
  | [] => match q.tail.reverse with 
    | x :: xs => some (x, ⟨xs, []⟩)
    | []      => none

def QueueData.rel (a b : QueueData α): Prop := a.toList = b.toList

def QueueSetoid (α : Type u): Setoid (QueueData α) := {
  r := QueueData.rel
  iseqv := {
    refl := by simp [QueueData.rel]
    symm := by intros _ _ p; simp [QueueData.rel]; rw [p]
    trans := by intros _ _ _ p q; simp [QueueData.rel]; rw [p, q] 
  }
}

def Queue (α : Type u) := Quotient (QueueSetoid α) 

def Queue.toList (q: Queue α): List α := 
  q.lift (·.toList) <| by intros; assumption

def Queue.send (q: Queue α) (x: α): Queue α := 
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
    
def Queue.pull (q: Queue α) : Option (α × Queue α) :=
  q.lift (fun qd => qd.pull.map (fun (a, xs) => (a, Quot.mk _ xs))) <| by
  simp [HasEquiv.Equiv]
  unfold Setoid.r
  intros a b p
  cases a; case mk ia ta =>
  cases b; case mk ib tb => 
  simp [QueueSetoid, QueueData.rel, QueueData.toList] at p
  let p1 := congrArg List.reverse p
  cases ia
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
          apply Quot.sound
          simp [QueueSetoid, QueueData.rel, QueueData.toList]
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
        apply Quot.sound
        simp [QueueSetoid, QueueData.rel, QueueData.toList]
        exact p.right
    . case cons ibh ibt =>
      simp at p
      rw [p.left]
      simp [Option.map, QueueData.pull]
      apply Quot.sound
      simp [QueueSetoid, QueueData.rel, QueueData.toList]
      exact p.right


-- instance: Inhabited (Queue α) where
--   default := ([], [])


  