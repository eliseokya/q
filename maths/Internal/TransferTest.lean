import Mathlib
import Internal.Core

namespace TransferTest

inductive Prim where
  | transfer
  deriving Repr, DecidableEq

abbrev Action := List Prim

structure State where
  dummy : Unit := ()

@[simp]
def step : Action → State → State := by
  intro _ σ; exact σ

open Contract

def spec : Spec := { State := State, Action := Action, step := step }

instance : HasId Action where
  idAct := []

instance : HasComp Action where
  compAct := List.append

instance : IsCategory spec := by
  refine { id_left := ?_, id_right := ?_, assoc := ?_ } <;> intros <;> simp [step, List.append_assoc]

end {}
@[simp]
def compilePrim : Prim → EVM.OpCode := fun _ => EVM.OpCode.CALL

@[simp]
def compile (act : Action) : EVM.Trace :=
  let n := act.length
  { ops    := List.repeat (EVM.OpCode.CALL) n,
    gas    := n,
    diff   := { updates := act.map (fun p => toString p) },
    status := EVM.ExecStatus.success }

open EVM

lemma compile_id : compile (HasId.idAct : Action) = idTrace := by
  simp [compile, HasId.idAct, idTrace]

lemma compile_pres (a b : Action) :
    comp (compile a) (compile b) = some (compile (List.append a b)) := by
  simp [compile, comp, List.length_append, List.map_append, List.repeat_append]

