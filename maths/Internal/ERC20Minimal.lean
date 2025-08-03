import Mathlib
import EVM.Trace
import Internal.Core

/-!
A **toy ERC-20 contract** used to validate the `Contract.Spec` framework.
For simplicity we ignore balances and gas; `step` is identity, so proofs are
trivial but exercise the machinery.
-/

open Contract

abbrev Address := String

namespace ERC20Minimal

/-- Primitive public actions for the toy token. -/
inductive Prim where
  | transfer (from to : Address) (amount : Nat)
  deriving Repr, DecidableEq

/-- `Action` is a list of primitive calls so that composition is list append. -/
abbrev Action := List Prim

/-- State carries a balance map.  We model balances as a function
from addresses to natural numbers for simplicity. -/
structure State where
  balances : Address → Nat

namespace State
/-- Helper: update balances for a transfer. Assumes sender has enough funds. -/
def transfer (σ : State) (from to : Address) (amt : Nat) : State :=
  {
    balances := fun a =>
      if h₁ : a = from then σ.balances a - amt
      else if h₂ : a = to then σ.balances a + amt
      else σ.balances a
  }
end State

/-- Apply a single primitive action. -/
@[simp]
def stepPrim : Prim → State → State
  | Prim.transfer from to amt, σ => σ.transfer from to amt

/-- Fold a list of actions left-to-right. -/
@[simp]
def step : Action → State → State
  | [], σ   => σ
  | (p :: ps), σ => step ps (stepPrim p σ)

/-- Package into a `Spec`. -/
def spec : Spec := { State := State, Action := Action, step := step }

instance : HasId Action where
  idAct := []

instance : HasComp Action where
  compAct := List.append

/-- Lemma: executing the empty action list is identity. -/
lemma step_nil (σ : State) : step [] σ = σ := by rfl

/-- Lemma: executing appended lists equals sequential execution. -/
lemma step_append (as bs : Action) (σ : State) :
    step (as ++ bs) σ = step bs (step as σ) := by
  induction as generalizing σ with
  | nil => simp [step]
  | cons a tl ih =>
      simp [step, ih, List.cons_append]

/-- Establish small category instance. -/
instance : IsCategory spec :=
by
  refine {
    id_left := ?_,
    id_right := ?_,
    assoc := ?_
  }
  · intro a σ; simp [HasComp.compAct, HasId.idAct, step_append, step_nil]
  · intro a σ; simpa [HasComp.compAct, HasId.idAct, step_append, step_nil, List.append_nil] using rfl
  · intro a b c σ; simp [HasComp.compAct, step_append, List.append_assoc]

/-- Compile a primitive into a single CALL opcode with dummy gas cost. -/
@[simp]
def compilePrim : Prim → EVM.OpCode := fun _ => EVM.OpCode.CALL

/-- Turn an action list into an `EVM.Trace`. -/
@[simp]
def compile (act : Action) : EVM.Trace :=
  let n := act.length
  {
    ops    := List.repeat (EVM.OpCode.CALL) n,
    gas    := n, -- 1 gas per call as placeholder
    diff   := { updates := act.map (fun p => toString p) },
    status := EVM.ExecStatus.success
  }

open EVM

/-- `compile` preserves identities. -/
lemma compile_id : compile (HasId.idAct : Action) = idTrace := by
  simp [compile, HasId.idAct, idTrace]

/-- `compile` preserves composition. -/
lemma compile_pres (a b : Action) :
    comp (compile a) (compile b) = some (compile (List.append a b)) := by
  simp [compile, comp, List.length_append, List.map_append, List.repeat_append]

end ERC20Minimal 