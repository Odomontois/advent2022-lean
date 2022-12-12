import Lean

class QueueData (α : Type u) where
  init: List α 
  tail: List α

def QueueData.toList (q: QueueData α): List α := q.init ++ q.tail.reverse

def QueueData.push (q: QueueData α) (a: α): QueueData α := {q with tail := a :: q.tail}

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

def Queue.push (q: Queue α) (x: α): Queue α := 
  q.lift (fun qd => Quot.mk _ (qd.push x)) <| by
    simp [HasEquiv.Equiv]
    unfold Setoid.r
    intros a b p
    cases a; case mk ia ta =>
    cases b; case mk ib tb => 
    simp [QueueData.push]
    apply Quot.sound
    simp [QueueSetoid, QueueData.rel, QueueData.toList]
    repeat rw [← List.append_assoc]
    simp [QueueSetoid, QueueData.rel, QueueData.toList] at p
    rw [p]    

-- def Queue.pop (q: Queue α) : Option (α × Queue α) :=
--   match q with
--   | (x ::xs, tail) => some (x, (xs, tail))
--   | ([], tail) => match tail.reverse with 
--     | x :: xs => some (x, (xs, []))
--     | []      => none

-- instance: Inhabited (Queue α) where
--   default := ([], [])


  