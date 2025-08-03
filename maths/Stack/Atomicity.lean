/--
Atomic bundles: those whose `forward` morphism is an isomorphism in the
(total) Grothendieck category.  Because our bicategory on `∫F` is thin,
`IsIso` is enough to guarantee an invertible 2-cell between the start and
finish states of the bundle.

We provide helpers to construct atomic bundles from:
* a single isomorphism (`ofIso`),
* a list of isomorphisms whose categorical composite is therefore iso
  (`ofIsoList`).
-/

import Stack.Bundles
import Stack.Invariant
import Mathlib.Tactic

open CategoryTheory

universe u

namespace Stack

/-- A bundle is *atomic* if its forward morphism is an isomorphism. -/
@[simp]
def isAtomic (B : Bundle) : Prop :=
  IsIso B.forward

-- Placeholder: additional constructors/lemmas will be added in later
-- sub-steps once concrete bundle building functions are available.

/-- If the forward morphism is an isomorphism and preserves an invariant P,
then the bundle is atomic and P holds at the finish. -/
lemma atomic_of_iso_preserving {P : Grothendieck.TotalObj → Prop}
    {B : Bundle}
    (hIso : IsIso B.forward)
    (hPres : Preserves P B.forward)
    (hStart : P B.start) :
    isAtomic B ∧ P B.finish := by
  constructor
  · exact hIso
  · exact hPres hStart

/-- Composition of isomorphisms preserving an invariant. -/
lemma atomic_of_comp_iso {P : Grothendieck.TotalObj → Prop}
    {A B C : Grothendieck.TotalObj}
    {f : A ⟶ B} {g : B ⟶ C}
    (hf : IsIso f) (hg : IsIso g)
    (hpf : Preserves P f) (hpg : Preserves P g)
    (hA : P A) :
    IsIso (f ≫ g) ∧ P C := by
  constructor
  · apply IsIso.comp_isIso
  · exact hpg (hpf hA)

end Stack 