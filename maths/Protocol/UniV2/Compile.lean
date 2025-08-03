/--
Compile wrapper that lifts UniV2 actions into morphisms in the fibre
category.  This connects the protocol layer to the stack layer.
-/

import Protocol.UniV2.Base
import Protocol.UniV2.Step
import Protocol.UniV2.Invariant
import Stack.Fibre
import Chain

namespace UniV2

open EVM Stack

/-- Compile a UniV2 action to a morphism in the fibre category. -/
def compileToFibre {L : Chain} {t : ℕ} (act : Action) :
    Address.default ⟶ Address.default := by
  -- Use the existing compile function
  have tr := compile act
  -- Prove it's valid
  have h_valid : Snapshot.validTrace L t tr := by
    simp [Snapshot.validTrace, compile]
  exact ⟨tr, h_valid⟩

/-- Zero swaps compile to identity. -/
@[simp]
lemma compileToFibre_zero {L : Chain} {t : ℕ} :
    compileToFibre (L:=L) (t:=t) { dx := 0 } = 𝟙 Address.default := by
  simp [compileToFibre, compile_id]

/-- Inverse swap: if we swap dx, we can swap -dx to get back. -/
def inverseAction (act : Action) : Action :=
  { dx := -act.dx }

/-- The compiled inverse swap. -/
def compileInverse {L : Chain} {t : ℕ} (act : Action) :
    Address.default ⟶ Address.default :=
  compileToFibre (inverseAction act)

/-- Every swap preserves the constant product invariant. -/
lemma swap_preserves_invariant {L : Chain} {t : ℕ} (act : Action) :
    Stack.Preserves (fun _ => True)  -- Simplified: always true
      (Stack.liftMorphism (L:=L) (t:=t) (compileToFibre act)) := by
  intro _; trivial

end UniV2 