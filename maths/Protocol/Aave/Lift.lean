/--
Stack-level lift of Aave collateral-ratio invariant.
-/

import Protocol.Aave.Invariant

namespace Aave

@[simp]
lemma healthy_preserved_total (acts : Action) (l : Ledger) (h : healthy l) :
    healthy (step acts l) := by
  exact healthy_preserved acts l h

end Aave 