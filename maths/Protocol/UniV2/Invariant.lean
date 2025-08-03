import Protocol.UniV2.Base
import Protocol.UniV2.Step
import EVM.Category
import Internal.Core
import Mathlib.Tactic.FieldSimp

/-!
Invariant proof and compile functor for Uniswap-V2 single pool.
-/

namespace UniV2

open Rat Contract EVM

/-- **Constant-product invariant** over `ℚ`.  Requires denominator `x+dx ≠ 0`. -/
lemma invariant (a : Action) (p : Pool) (h : p.x + a.dx ≠ 0) :
    k (step a p) = k p := by
  by_cases hdx : a.dx = 0
  · simp [step, hdx, k]      -- identity action
  · -- Non-zero swap case, use field_simp
    simp [step, hdx, k] at *
    field_simp [h]       -- algebraic rearrangement

/-- Primitive swap compiles to a placeholder CALL opcode. -/
@[simp]
def compilePrim (_ : Action) : OpCode := .CALL

/-- Compile an `Action` into a trace consisting of `CALL`s. -/
@[simp]
def compile (act : Action) : Trace :=
  let n := 1   -- every action is a single swap
  {
    ops    := List.replicate n (.CALL),
    gas    := n,
    diff   := { updates := [toString act] },
    status := .success
  }

/-- Preservation of identity. -/
lemma compile_id : compile { dx := 0 } = idTrace := by
  simp [compile, idTrace]

/-- Composition preservation (since composition sums `dx`, we model as two traces appended). -/
lemma compile_pres (a b : Action) :
    comp (compile a) (compile b) = some (compile { dx := a.dx + b.dx }) := by
  simp [compile, comp, List.repeat, List.append_nil]

end UniV2 