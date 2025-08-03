import Mathlib
import Internal.Core
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Uniswap V2 Constant-Product Invariant (Prototype)

We model a single liquidity pool with reserves `