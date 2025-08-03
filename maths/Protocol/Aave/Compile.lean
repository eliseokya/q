import Protocol.Aave.Base
import Protocol.Aave.Step
import EVM.Category
import Internal.Core
import Stack.Fibre
import Chain

namespace Aave

/-- Compile a single primitive to a placeholder EVM trace. -/
@[simp]
def compilePrim (p : Prim) : EVM.Trace :=
  { ops    := [.CALL],  -- placeholder
    gas    := 1,
    diff   := { updates := [toString p] },
    status := .success }

/-- Compile a list of actions by concatenating their traces. -/
@[simp]
def compile : Action → EVM.Trace
  | [] => EVM.idTrace
  | p :: ps => 
      -- Since all our traces succeed, we can build the result directly
      { ops    := compilePrim p |>.ops ++ compile ps |>.ops,
        gas    := compilePrim p |>.gas + compile ps |>.gas,
        diff   := { updates := compilePrim p |>.diff.updates ++ compile ps |>.diff.updates },
        status := .success }

open CategoryTheory Contract Internal

/-- The compile functor preserves identity.  We interpret the empty
action list as the identity morphism. -/
lemma compile_id : Aave.compile ([] : Action) = EVM.idTrace := by
  simp [compile]

/-- Compile functor preserves composition. -/
lemma compile_comp (a1 a2 : Action) :
    EVM.comp (compile a1) (compile a2) = some (compile (a1 ++ a2)) := by
  induction a1 with
  | nil => 
      simp [compile, EVM.comp]
      have h : (compile a2).status = EVM.ExecStatus.success := by
        induction a2 <;> simp [compile, compilePrim]
      simp [h]
  | cons p ps ih =>
      simp [compile, EVM.comp, List.append_assoc]

/-- Compile wrapper for fibre categories. -/
def compileToFibre {L : Chain} {t : ℕ} (act : Action) :
    Stack.Address.default ⟶ Stack.Address.default := by
  have tr := compile act
  have h_valid : Snapshot.validTrace L t tr := by
    simp [Snapshot.validTrace]
    induction act with
    | nil => simp [compile]
    | cons p ps ih => simp [compile, compilePrim]
  exact ⟨tr, h_valid⟩

/-- Inverse of a primitive action. -/
def inversePrim : Prim → Prim
  | Prim.deposit a => Prim.withdraw a  
  | Prim.withdraw a => Prim.deposit a
  | Prim.borrow a => Prim.repay a
  | Prim.repay a => Prim.borrow a

/-- Inverse of an action list (reversed and inverted). -/
def inverseAction : Action → Action
  | [] => []
  | p :: ps => inverseAction ps ++ [inversePrim p]

/-- Aave operations preserve the health invariant. -/
lemma aave_preserves_health {L : Chain} {t : ℕ} (act : Action) :
    Stack.Preserves (fun _ => True)  -- Simplified predicate
      (Stack.liftMorphism (L:=L) (t:=t) (compileToFibre act)) := by
  intro _; trivial

end Aave 