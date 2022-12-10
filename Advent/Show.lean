import Lean
open Lean
instance [ToJson α] : ToString α where
  toString := ToString.toString ∘ ToJson.toJson 