/--
Shift functor on the base category `Timeᵒᵖ` adding a constant delay `δ`
(to the underlying natural number) on objects and mapping arrows via
`Nat.add_le_add_right`.
-/

import Time.Category
import Mathlib.CategoryTheory.Functor

open CategoryTheory

namespace Bridge

/-- Add `δ` blocks of delay to every block-height index. -/
@[simp]
def shiftFunctor (δ : ℕ) : (Time)ᵒᵖ ⥤ (Time)ᵒᵖ where
  obj := fun t => Opposite.op (Opposite.unop t + δ)
  map := by
    intro t s h
    -- In terms of `≤` proofs: we need `unop s + δ ≤ unop t + δ`.
    exact (Nat.add_le_add_right h δ)
  map_id := by
    intro t; simp
  map_comp := by
    intro a b c f g; rfl

end Bridge 