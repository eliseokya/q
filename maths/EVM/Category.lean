import Mathlib
import EVM.Trace

open EVM

/-! # Execution Category 𝓔_EVM (partial)

This file defines the (partial) composition operation on traces and provides
an identity trace.  Proofs of associativity and identity laws will follow in
Phase 1.3. -/

namespace EVM

/-- The *identity trace*: does nothing, consumes zero gas, changes no state,
and succeeds. -/
@[simp]
def idTrace : Trace where
  ops    := []
  gas    := 0
  diff   := { updates := [] }
  status := ExecStatus.success

/-- Partial composition of two traces.  Defined **only** when both traces
end in `success`.  Returns `none` if either trace has status `revert`. -/
@[simp]
def comp (t₁ t₂ : Trace) : Option Trace :=
  if h : t₁.status = ExecStatus.success ∧ t₂.status = ExecStatus.success then
    some {
      ops    := t₁.ops ++ t₂.ops,
      gas    := t₁.gas + t₂.gas,
      diff   := { updates := t₁.diff.updates ++ t₂.diff.updates },
      status := ExecStatus.success
    }
  else
    none

/-- Composition when both traces succeeded reduces to concatenation. -/
lemma comp_some {t₁ t₂ : Trace}
    (h₁ : t₁.status = ExecStatus.success)
    (h₂ : t₂.status = ExecStatus.success) :
  comp t₁ t₂ = some {
      ops    := t₁.ops ++ t₂.ops,
      gas    := t₁.gas + t₂.gas,
      diff   := { updates := t₁.diff.updates ++ t₂.diff.updates },
      status := ExecStatus.success } := by
  simp [comp, h₁, h₂]

/-- Left identity law for successful traces. -/
lemma id_left {t : Trace} (h : t.status = ExecStatus.success) :
    comp idTrace t = some t := by
  simp [idTrace, comp, h]

/-- Right identity law for successful traces. -/
lemma id_right {t : Trace} (h : t.status = ExecStatus.success) :
    comp t idTrace = some t := by
  simp [idTrace, comp, h, List.append_nil, Nat.add_zero]

/-- Associativity of `comp` on successful traces. -/
lemma comp_assoc {a b c : Trace}
    (ha : a.status = ExecStatus.success)
    (hb : b.status = ExecStatus.success)
    (hc : c.status = ExecStatus.success) :
  let ab   := { ops := a.ops ++ b.ops,
                gas := a.gas + b.gas,
                diff := { updates := a.diff.updates ++ b.diff.updates },
                status := ExecStatus.success }
  let bc   := { ops := b.ops ++ c.ops,
                gas := b.gas + c.gas,
                diff := { updates := b.diff.updates ++ c.diff.updates },
                status := ExecStatus.success }
  comp ab c = comp a bc := by
  simp [comp, ha, hb, hc, List.append_assoc, Nat.add_assoc]

end EVM 