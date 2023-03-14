def peirceEq: (forall a, a \/ ¬ a) ↔ (forall p q,((p -> q) -> p) -> p) := by
constructor
. intros lem P Q f 
  cases lem P
  . assumption
  . case inr notp => 
    apply f
    intro p
    contradiction
. intros peirce A
  apply peirce _ False
  intro notOr
  apply Or.inr
  intro a
  apply notOr (Or.inl a)


      