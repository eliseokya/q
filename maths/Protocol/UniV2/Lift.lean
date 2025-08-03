/--
Lifting the constant-product invariant proven in `Invariant.lean` into
stack-level reasoning is a no-op for now, because the invariant is purely
algebraic and independent of the categorical context.  We simply re-export
`UniV2.invariant` under a name that fits the stack-layer naming scheme.
-/

import Protocol.UniV2.Invariant

namespace UniV2

/-- Stack-level constant-product invariant (identical to the fibre invariant).
In later refinements this file will wrap the statement with the inclusion
`fibreFunctor`, but at the moment there is nothing to do. -/
@[simp]
lemma invariant_total (a : Action) (p : Pool) (h : p.x + a.dx ≠ 0) :
    k (step a p) = k p := by
  exact invariant a p h

end UniV2 