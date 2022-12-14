namespace Decidable

instance {α β} : HOr (Decidable α) (Decidable β) (Decidable (α ∨ β)) where
  hOr a b := match a with 
  | isTrue ya => isTrue <| Or.inl ya
  | isFalse na => match b with 
    | isTrue yb => isTrue <| Or.inr yb
    | isFalse nb => isFalse <| by intro p ; cases p <;> contradiction


instance {α β} : HAnd (Decidable α) (Decidable β) (Decidable (α ∧ β)) where
  hAnd a b := match a with 
  | isFalse na => isFalse <| fun p => na p.left
  | isTrue ya => match b with 
    | isFalse nb => isFalse <| fun p => nb p.right
    | isTrue yb => isTrue <| And.intro ya yb
end Decidable