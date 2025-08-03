import Protocol.UniV2.Base
import Protocol.UniV2.Step
import Internal.Core

namespace UniV2

open Contract

/-- Package into a Spec so swaps compose under addition of `dx`. -/

def spec : Spec := { State := Pool, Action := Action, step := step }

instance : HasId Action where
  idAct := { dx := 0 }

instance : HasComp Action where
  compAct a b := { dx := a.dx + b.dx }

instance : IsCategory spec := by
  refine {
    id_left := ?_,
    id_right := ?_,
    assoc := ?_
  }
  all_goals
    intro a s; cases a; simp [HasId.idAct, HasComp.compAct, step]

end UniV2 