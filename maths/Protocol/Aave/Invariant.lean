import Protocol.Aave.Base
import Protocol.Aave.Step

namespace Aave

@[simp]
lemma healthy_after_deposit {l : Ledger} {a : ℚ} (h : healthy l) :
    healthy (Aave.applyPrim (Prim.deposit a) l) := by
  simp [Aave.applyPrim, healthy] at *; linarith

@[simp]
lemma healthy_after_borrow {l : Ledger} {a : ℚ} (h : healthy l) :
    healthy (Aave.applyPrim (Prim.borrow a) l) := by
  simp [Aave.applyPrim, healthy] at *
  by_cases hcond : l.c ≥ l.d + a
  · simp [hcond, healthy] at *; linarith [h, hcond]
  · simp [hcond, healthy] at *; exact h

@[simp]
lemma healthy_after_repay {l : Ledger} {a : ℚ} (h : healthy l) :
    healthy (Aave.applyPrim (Prim.repay a) l) := by
  simp [Aave.applyPrim, healthy] at *
  have hmax : max 0 (l.d - a) ≤ l.d := by
    exact max_le_left _ _
  linarith

/-- Preservation of collateral ratio `c ≥ d` for any action list. -/
lemma healthy_preserved (acts : Action) (l : Ledger) (h : healthy l) :
    healthy (step acts l) := by
  induction acts with
  | nil => simpa [step] using h
  | cons a tl ih =>
      simp [step] at ih ⊢
      cases a with
      | deposit amt => exact ih (healthy_after_deposit h)
      | borrow  amt => exact ih (healthy_after_borrow h)
      | repay   amt => exact ih (healthy_after_repay h)

end Aave 