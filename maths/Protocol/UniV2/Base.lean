import Mathlib

/-!
UniV2.Base – Fundamental data types for a single Uniswap V2 pool.
-/

namespace UniV2

abbrev Address := String

/-- Reserves of a two-token pool; rational numbers for easier algebra. -/
structure Pool where
  x : ℚ
  y : ℚ
  deriving Repr

@[simp] def k (p : Pool) : ℚ := p.x * p.y

/-- Swap action: user sends `dx` of token X into the pool. -/
structure Swap where
  dx : ℚ
  deriving Repr

abbrev Action := Swap

end UniV2