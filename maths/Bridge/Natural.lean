/--
Bridge natural transformations between per-chain presheaves.
For now we give a minimal definition – a natural transformation
between two presheaves – and basic helper lemmas.  Concrete bridge
instances (HTLB, zk-proof, threshold-sig, etc.) will inhabit this
structure in later phases.
-/

import Time.Category
import Stack.Global
import Chain
import Mathlib.CategoryTheory.Functor
import Mathlib.CategoryTheory.NatTrans

universe u

namespace Bridge

open CategoryTheory

/-- A *bridge* between chains `L` and `L'` is (for now) simply a natural
transformation between their Cat-valued presheaves over `Timeᵒᵖ`.
Later we will enrich this with delay `δ` and proof objects. -/
structure NT (L L' : Chain) where
  η : Stack.FL L ⟶ Stack.FL L'

end Bridge 