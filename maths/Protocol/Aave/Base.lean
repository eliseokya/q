import Mathlib

/-!
Aave v3 – minimal ledger model for a single user and asset.
We track collateral `c` and debt `d` as non-negative rationals.
Health requirement: `c ≥ d` (collateral ratio ≥ 1).
-/

namespace Aave

structure Ledger where
  c : ℚ  -- collateral supplied
  d : ℚ  -- debt borrowed
  deriving Repr

@[simp] def healthy (l : Ledger) : Prop := l.c ≥ l.d


end Aave 