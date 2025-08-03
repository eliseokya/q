/--
`FibreCat L t` is the category of EVM traces on chain `L` that have
**already succeeded** by block height `t`.  Objects are addresses
(for now we use a single placeholder address).  Morphisms are successful
execution traces.
-/

import Chain
import Snapshot
import EVM.Category
import Mathlib.CategoryTheory.Category

open CategoryTheory Snapshot EVM

universe u

namespace Stack

/-- For now we model a single address per chain. -/
inductive Address : Type
  | default

/-- Category of successful EVM traces at a given block height. -/
def FibreCat (L : Chain) (t : ℕ) : Type := Address

instance (L : Chain) (t : ℕ) : SmallCategory (FibreCat L t) where
  Hom A B := { tr : Trace // validTrace L t tr }
  id A := ⟨idTrace, by simp [validTrace, idTrace]⟩
  comp {A B C} f g := by
    -- Compose the underlying traces
    have hf : f.val.status = ExecStatus.success := f.property
    have hg : g.val.status = ExecStatus.success := g.property
    -- Use EVM.comp which returns Option Trace
    have h_comp := comp f.val g.val
    -- Extract the successful composition
    have h_some : ∃ tr, comp f.val g.val = some tr := by
      simp [comp, hf, hg]
      use { ops := f.val.ops ++ g.val.ops,
            gas := f.val.gas + g.val.gas,
            diff := { updates := f.val.diff.updates ++ g.val.diff.updates },
            status := ExecStatus.success }
    obtain ⟨tr, htr⟩ := h_some
    -- Prove the composed trace is valid
    have h_valid : validTrace L t tr := by
      rw [← htr]
      simp [comp, hf, hg] at htr
      cases htr
      simp [validTrace]
    exact ⟨tr, h_valid⟩

end Stack 