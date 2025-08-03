import Mathlib

/-!
Compound – minimal single-asset ledger with interest accrual.
-/

namespace Compound

/-- Supply `s` and borrow `b` expressed in rational units. -/
structure Ledger where
  s : ℚ
  b : ℚ
  deriving Repr

@[simp] def healthy (l : Ledger) : Prop := l.s ≥ l.b

end Compound 