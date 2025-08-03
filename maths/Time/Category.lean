import Mathlib.CategoryTheory.Category
import Mathlib.CategoryTheory.Preorder

/-!
# Time Category 𝒯

We represent block heights as natural numbers.  Morphisms are given by the
ordering `t ≤ s`, yielding a thin category where at most one morphism exists
between any two objects.
-/

open CategoryTheory

namespace Time

/-- A convenient alias for the category of natural numbers with morphisms given by `≤`. -/
abbrev TimeCat : Type := ℕ

/-- The small category whose objects are natural numbers and whose morphisms are
`≤` proofs.  This instance is provided by `Mathlib` for every preorder. -/
instance : SmallCategory ℕ := inferInstance

@[simp] lemma id_hom (t : ℕ) : (𝟙 t : t ≤ t) := le_rfl

@[simp] lemma comp_hom {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c) :
    ((h₁ ≫ h₂) : a ≤ c) = Nat.le_trans h₁ h₂ := rfl

@[simp] lemma antisymm_eq {a b : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b :=
  Nat.le_antisymm h₁ h₂

end Time 