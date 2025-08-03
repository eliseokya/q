import Time.Category
import Mathlib.CategoryTheory.Sheaf

/-!
A very simple Grothendieck topology on `Timeᵒᵖ`: every sieve is a covering
sieve (the indiscrete topology).  This suffices for initial sheaf proofs.
-/

open CategoryTheory Opposite

namespace Time

/-- Indiscrete (coarsest) Grothendieck topology on any category: every sieve
is covering. -/
noncomputable def indiscreteTopology (C : Type) [Category C] : GrothendieckTopology C :=
{ sieves := fun U S => True,
  top_mem' := by intro U; trivial,
  pullback_stable' := by intro U S hV f; trivial,
  transitive' := by intro U S hS hcover; trivial }

/-- The topology we use on `Timeᵒᵖ` is the indiscrete one. -/
noncomputable def τ : GrothendieckTopology ((Opposite ℕ)) :=
  indiscreteTopology (Opposite ℕ)

end Time 