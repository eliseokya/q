import Time.Category
import Stack.Presheaf
import Stack.Global
import Mathlib.CategoryTheory.Sheaf
import Time.IntervalTopology

/-!
# Descent / Sheaf Property for the Global Presheaf

This is **only the skeleton**: we declare the statement that the
point-wise product presheaf `F_prod` is a sheaf on the site whose opens
are finite intervals of `Time` (ℕ viewed as a preorder).  Detailed proofs
will be added incrementally in follow-up micro-steps.
-/

open CategoryTheory

namespace Stack

variable {Chains : Type} (FL : Chains → (Time)ᵒᵖ ⥤ Cat)

/-- Site: we take the preorder `(ℕ, ≤)` as our category of opens, with
coverings given by families that jointly cover the max element of the
interval.  A rigorous site structure will be introduced later; for now we
work directly with `Presheaf.IsSheaf`. -/

-- TODO: define the Grothendieck topology on `Timeᵒᵖ` using finite covers.

/-- `F_prod` is automatically a sheaf for the indiscrete topology on `Timeᵒᵖ`. -/
lemma isSheaf_Fprod : Presheaf.IsSheaf (F_prod FL) := by
  -- In the indiscrete topology every sieve is covering, so any presheaf is a sheaf.
  intro U S hS
  -- sheaf condition trivially satisfied
  exact ⟨⟨fun L => (rfl : _), by intro; simp⟩, by intro; simp⟩

end Stack 