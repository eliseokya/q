import Mathlib
import EVM.Trace
import Internal.Core

/-!
# ERC-20 Holder Category (𝓣₍₂₀₎) and Strong Monoidal Functor to 𝓔_EVM

This is a *minimal* formalisation sufficient to demonstrate Phase 3.1.
Objects are addresses; morphisms are token‐transfer instructions wrapped in
lists so that composition is list append.  We prove the category laws and
provide a `compile` functor into base EVM traces.  A true *strong monoidal*
proof (tensor product, unit object, coherence) will follow in Phase 3.2.
-/

namespace ERC20

abbrev Address := String

/-- Primitive ERC-20 operation: transfer an `amount` from `from` to `to`. -/
structure Prim where
  from   : Address
  to     : Address
  amount : Nat
  deriving Repr, DecidableEq

abbrev Action := List Prim

/-- Objects of 𝓣₂₀ are addresses.  Hom‐set between any two addresses is `Action`
filtering on *from* and *to* fields.  For simplicity we do **not** index the
hom‐set here; we just treat every `Action` as a morphism regardless of
endpoints and rely on run-time fields.  This keeps the example lightweight. -/

/-- Identity action is the empty list (no transfer). -/
instance : Contract.HasId Action where
  idAct := []

/-- Composition is list append. -/
instance : Contract.HasComp Action where
  compAct := List.append

/-- Step function for token actions: abstract state not modelled yet; we use
identity.  This is acceptable for Phase 3.1 because only categorical laws are
required. -/
structure State where
  dummy : Unit := ()

open Contract

@[simp]
def step : Action → State → State := by
  intro _ σ; exact σ

/-- Package into a `Spec`. -/
def spec : Spec := { State := State, Action := Action, step := step }

/-- Proof that list append with empty list forms a small category. -/
instance : IsCategory spec :=
by
  refine {
    id_left := ?_,
    id_right := ?_,
    assoc := ?_
  }
  · intro a σ; simp [HasComp.compAct, HasId.idAct, step]
  · intro a σ; simp [HasComp.compAct, HasId.idAct, step, List.append_nil]
  · intro a b c σ; simp [HasComp.compAct, step, List.append_assoc]

/-- Compile a primitive transfer into a single CALL opcode (placeholder). -/
@[simp]
def compilePrim (_ : Prim) : EVM.OpCode := .CALL

/-- Translate an `Action` into an `EVM.Trace`.  Gas cost = length; state diff
is a stringified log of transfers; always succeeds. -/
@[simp]
def compile (act : Action) : EVM.Trace :=
  let n := act.length
  {
    ops    := List.repeat (.CALL) n,
    gas    := n,
    diff   := { updates := act.map (fun p => toString p) },
    status := .success
  }

open EVM

/-- Identity preservation. -/
lemma compile_id : compile (Contract.HasId.idAct : Action) = idTrace := by
  simp [compile, Contract.HasId.idAct, idTrace]

/-- Composition preservation. -/
lemma compile_pres (a b : Action) :
    comp (compile a) (compile b) = some (compile (List.append a b)) := by
  simp [compile, comp, List.length_append, List.map_append, List.repeat_append]

end ERC20 