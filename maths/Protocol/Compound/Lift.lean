/--
Stack-level lift of Compound healthy_preserved_with_margin.
-/

import Protocol.Compound.Invariant

namespace Compound

@[simp]
lemma healthy_preserved_total (acts : Action) (l : Ledger)
    (h_margin : l.s ≥ (1 + r) ^ accCount acts * l.b)
    (hb : 0 ≤ l.b) :
    healthy (step acts l) := by
  exact healthy_preserved_with_margin acts l h_margin hb

end Compound 