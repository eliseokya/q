/--
Toy example: identity bundle that demonstrates the atomicity machinery
compiles. Once we have real EVM traces in the fibres, this will be
replaced with actual flash-loan examples.
-/

import Stack.Bundles
import Stack.Atomicity

open CategoryTheory Grothendieck

namespace Examples

/-- Pick any object in ∫F (block 0, chain polygon, trivial state). -/
def startObj : TotalObj := ⟨0, fun L => PUnit.unit⟩

/-- Identity bundle: does nothing, succeeds trivially. -/
def noOpBundle : Stack.Bundle :=
{ start     := startObj,
  finish    := startObj,
  forward   := id startObj,
  repay     := id startObj,
  atomicity := by simp }

/-- The identity bundle is trivially atomic. -/
example : Stack.isAtomic noOpBundle := by
  simp [Stack.isAtomic]

end Examples 