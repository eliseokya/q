/--
Cross-chain Hashed Time Locked Bridge (HTLB) example.  This is a stub
that simply copies the *identity* morphisms from chain `L` to chain
`L'`, but with a fixed latency `δ` encoded via precomposition with the
`shiftFunctor δ` on the time index.

Because the current fibre categories are constant (PUnit placeholder),
identity components satisfy naturality automatically.  This file shows
how to build a `Bridge` value for two *distinct* chains.
-/

import Bridge.Types
import Bridge.Shift
import Stack.Presheaf
import Chain
import Mathlib.CategoryTheory.NatIso

namespace Bridge

open CategoryTheory

/-- Helper: target functor precomposed with a block-delay shift. -/
@[simp]
def shifted (δ : ℕ) (L' : Chain) : (Time)ᵒᵖ ⥤ Cat :=
  (Bridge.shiftFunctor δ) ⋙ Stack.FL L'

/-- Identity-on-objects natural transformation `FL L ⟶ shifted δ L'`.
Since all fibres are `PUnit` placeholders, we simply take identities. -/
@[simp]
noncomputable def htlbNatTrans (δ : ℕ) (L L' : Chain) :
    Stack.FL L ⟶ shifted δ L' where
  app := fun t => 𝟙 _
  naturality := by
    intro t s h; simp

/-- Stub HTLB bridge from `L` to `L'` with delay `δ`. -/
@[simp]
noncomputable def HTLBCross (δ : ℕ) (L L' : Chain) : Bridge.Bridge L L' where
  δ := δ
  nt := { η := htlbNatTrans δ L L' }

end Bridge 