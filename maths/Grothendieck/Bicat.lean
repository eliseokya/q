import Grothendieck.Construction
import Mathlib.CategoryTheory.Bicategory.Thin

/-!
Thin bicategory structure on the Grothendieck total category.
For now we only declare 2-morphisms as equalities of 1-morphisms and supply
identity and vertical composition so the file compiles.  Coherence data is
provided automatically by `Thin`.
-/

open CategoryTheory

namespace Grothendieck

abbrev Obj := TotalObj
abbrev Hom := Hom

/-- 2-morphisms are equalities of 1-morphisms (thin bicategory). -/
abbrev TwoMor {A B : Obj} (f g : Hom A B) : Type := f = g

@[simp] def id₂ {A B : Obj} {f : Hom A B} : TwoMor f f := rfl

@[simp] def vcomp {A B : Obj} {f g h : Hom A B}
    (η₁ : TwoMor f g) (η₂ : TwoMor g h) : TwoMor f h :=
  Eq.trans η₁ η₂

/-- Thin bicategory instance provided by mathlib. -/
instance : Bicategory Obj :=
  Thin.bicategory

end Grothendieck 