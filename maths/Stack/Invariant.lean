/--
Generic machinery for reasoning about invariants of objects in the total
Grothendieck category `∫F`.

`Preserves P f` means the morphism `f` carries objects satisfying the
predicate `P` to objects again satisfying `P`.

We prove that preservation is closed under identity and composition, so
once every arrow in a bundle preserves an invariant, the whole bundle
composite also preserves it.
-/

import Grothendieck.Construction

open CategoryTheory

universe u

namespace Stack

type_synonym Obj := Grothendieck.TotalObj

def Hom := Grothendieck.Hom

/-- Predicate on objects of the total category. -/
variable (P : Obj → Prop)

/-- A morphism preserves an invariant `P` if whenever `P` holds at the
source object, it holds at the target object. -/
@[simp]
def Preserves {A B : Obj} (f : Hom A B) : Prop :=
  ∀ hA : P A, P B

namespace Preserves

variable {P}

@[simp]
lemma id (A : Obj) : Preserves P (Grothendieck.id A) :=
  fun hA => hA

@[simp]
lemma comp {A B C : Obj} {f : Hom A B} {g : Hom B C}
    (hf : Preserves P f) (hg : Preserves P g) :
    Preserves P (f ≫ g) :=
  fun hA =>
    have hB := hf hA
    hg hB

end Preserves

end Stack 