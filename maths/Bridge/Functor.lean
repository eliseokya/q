import Bridge.Types
import Bridge.Shift
import Stack.Presheaf
import Mathlib.CategoryTheory.Functor

/-!
Bridges as functors between chain presheaves, handling time delays.
-/

namespace Bridge

open CategoryTheory

/-- Convert a bridge to a functor between presheaves.
The functor incorporates the delay by pre-composing with the shift functor. -/
def toFunctor (b : Bridge) : Stack.FL b.source ⟶ Stack.FL b.target :=
  -- The bridge maps from source at time t to target at time t+δ
  -- This is achieved by composing the NT with the shift
  b.nt.η ≫ whiskerLeft (Stack.FL b.target) (shiftFunctor b.δ).op

/-- Identity bridges give identity functors (up to the shift). -/
lemma id_bridge_functor (L : Chain) : 
    toFunctor (htlbBridge L L 0 "" 1) = 𝟙 (Stack.FL L) := by
  simp [toFunctor, htlbBridge, shiftFunctor]
  -- When δ = 0, shift is identity
  sorry  -- requires showing shift 0 = id

/-- Composition of bridges. -/
def compose (b₁ : Bridge) (b₂ : Bridge) (h : b₁.target = b₂.source) : Bridge where
  source := b₁.source
  target := b₂.target
  δ := b₁.δ + b₂.δ
  proof := match b₁.proof, b₂.proof with
    | .htlb h₁ t₁, .htlb h₂ t₂ => .htlb (h₁ ++ h₂) (t₁ + t₂)
    | .zkSnark p₁ i₁, .zkSnark p₂ i₂ => .zkSnark (p₁ ++ p₂) (i₁ ++ i₂)
    | .thresholdSig s₁ t₁, .thresholdSig s₂ t₂ => .thresholdSig (s₁ ++ s₂) (min t₁ t₂)
    | _, _ => b₁.proof  -- fallback for mixed types
  nt := by
    -- Compose the natural transformations with appropriate shifts
    cases h
    exact NT.mk (fun t obj => b₂.nt.apply t (b₁.nt.apply t obj))

/-- Bridge functors preserve the presheaf structure. -/
lemma bridge_preserves_restriction (b : Bridge) (t s : ℕ) (h : t ≤ s) :
    toFunctor b ≫ Stack.FL b.target |>.map (homOfLE h).op = 
    Stack.FL b.source |>.map (homOfLE h).op ≫ toFunctor b := by
  -- This is the naturality condition
  sorry  -- requires unfolding definitions

end Bridge 