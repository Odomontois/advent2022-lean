import Lean
open Lean

instance : ToJson Char where
  toJson c := c.toString

instance [ToJson α] : ToString α where
  toString := ToString.toString ∘ ToJson.toJson 