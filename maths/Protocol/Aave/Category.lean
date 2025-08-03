import Protocol.Aave.Base
import Protocol.Aave.Step
import Protocol.Aave.Invariant
import Internal.Core

namespace Aave

open Contract

/-- Package Spec. -/
def spec : Spec := { State := Ledger, Action := Action, step := step }

instance : IsCategory spec := by
  refine { id_left := ?_, id_right := ?_, assoc := ?_ } <;> intros <;> simp [HasId.idAct, HasComp.compAct, step]

-- health invariant lemma available via Protocol.Aave.Invariant

end Aave 