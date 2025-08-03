import Grothendieck.Construction
import Mathlib.CategoryTheory.Bicategory

/-!
# 2-Morphisms in the Grothendieck Construction

This file adds 2-morphisms to make the total category into a bicategory.
2-morphisms witness different paths between the same endpoints.
-/

namespace Grothendieck

open CategoryTheory

/-- A 2-morphism between parallel 1-morphisms f, g : A ⟶ B in the total category.
It consists of a family of 2-morphisms in each fibre category that are
compatible with the time component. -/
structure TwoMorphism {A B : TotalObj} (f g : Hom A B) where
  -- Since f and g have the same time components (f.t_le = g.t_le),
  -- we need a 2-morphism in the fibre
  η : f.α ⟹ g.α
  -- No additional compatibility needed since time components are equal

notation f " ⟹ " g => TwoMorphism f g

/-- Identity 2-morphism. -/
def TwoMorphism.id {A B : TotalObj} (f : Hom A B) : f ⟹ f where
  η := 𝟙 f.α

/-- Vertical composition of 2-morphisms. -/
def TwoMorphism.vcomp {A B : TotalObj} {f g h : Hom A B} 
    (α : f ⟹ g) (β : g ⟹ h) : f ⟹ h where
  η := α.η ≫ β.η

notation α " ⊚ " β => TwoMorphism.vcomp α β

/-- Horizontal composition of 2-morphisms. -/
def TwoMorphism.hcomp {A B C : TotalObj} {f₁ g₁ : Hom A B} {f₂ g₂ : Hom B C}
    (α : f₁ ⟹ g₁) (β : f₂ ⟹ g₂) : (comp f₁ f₂) ⟹ (comp g₁ g₂) where
  η := by
    -- We need to construct a 2-morphism between the compositions
    -- This uses the horizontal composition in the fibre categories
    simp [comp]
    -- The morphism goes between:
    -- (F.map f₁.t_le).map f₂.α ≫ f₁.α  and
    -- (F.map g₁.t_le).map g₂.α ≫ g₁.α
    -- We use whiskering
    exact (Stack.F_prod.map (Opposite.op f₁.t_le)).map β.η ≫ α.η

notation α " ⊗ " β => TwoMorphism.hcomp α β

/-- Left whiskering: compose a 2-morphism on the left with a 1-morphism. -/
def TwoMorphism.whiskerLeft {A B C : TotalObj} (f : Hom A B) {g h : Hom B C}
    (α : g ⟹ h) : (comp f g) ⟹ (comp f h) :=
  hcomp (id f) α

/-- Right whiskering: compose a 2-morphism on the right with a 1-morphism. -/
def TwoMorphism.whiskerRight {A B C : TotalObj} {f g : Hom A B} 
    (α : f ⟹ g) (h : Hom B C) : (comp f h) ⟹ (comp g h) :=
  hcomp α (id h)

/-- A 2-morphism is invertible if its component in the fibre is an isomorphism. -/
def TwoMorphism.IsIso {A B : TotalObj} {f g : Hom A B} (α : f ⟹ g) : Prop :=
  IsIso α.η

/-- The inverse of an invertible 2-morphism. -/
noncomputable def TwoMorphism.inv {A B : TotalObj} {f g : Hom A B} 
    (α : f ⟹ g) [IsIso α.η] : g ⟹ f where
  η := inv α.η

/-- Two 1-morphisms are isomorphic if there's an invertible 2-morphism between them. -/
def HomIsomorphic {A B : TotalObj} (f g : Hom A B) : Prop :=
  ∃ (α : f ⟹ g), α.IsIso

notation f " ≅₂ " g => HomIsomorphic f g

end Grothendieck 