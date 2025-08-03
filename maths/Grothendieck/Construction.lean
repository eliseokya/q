import Time.Category
import Stack.Global
import Chain
import Mathlib.CategoryTheory.Category

/-!
Skeleton for the Grothendieck construction ∫ₜ F(t).
Now uses the concrete `Chain` enumeration type.
-/

open CategoryTheory

universe u

namespace Grothendieck

/-- Objects of the total category (Grothendieck construction) are pairs
`(t, x)` where `t : ℕ` is a block height (object in the base category
`Time`) and `x` is an object of the fibre category `F_prod` above `t`. -/
abbrev TotalObj := Σ t : ℕ, Stack.F_prod.obj (Opposite.op t)

open CategoryTheory

/-- Morphisms `(t, x) ⟶ (s, y)` consist of
1. a proof `h : t ≤ s` (arrow in the base category `Time`), and
2. a morphism in the fibre category from the *restriction* of `y` along
   `h` to `x`.

The direction matches the usual category-of-elements for a contravariant
functor: objects at later times can be *restricted back* to earlier
times. -/
structure Hom (A B : TotalObj) : Type where
  t_le : A.1 ≤ B.1
  α    : (Stack.F_prod.map (Opposite.op t_le)).obj B.2 ⟶ A.2

@[ext]
lemma Hom.ext (f g : Hom A B)
    (h₁ : f.t_le = g.t_le)
    (h₂ : by
        -- after rewriting by `h₁` the fibre morphisms live in the same
        -- hom-set, so we can compare them directly
        cases h₁
        exact f.α = g.α) :
    f = g := by
  cases f; cases g; cases h₁; cases h₂; rfl

/-- Identity morphism: the time component is `le_rfl`, and the fibre
arrow is the identity (after recognising that the restriction functor
acts as the identity on objects when `h = refl`). -/
@[simp] def id (A : TotalObj) : Hom A A where
    t_le := le_rfl
    α    := by
      -- `le_rfl` corresponds to the identity arrow in `Timeᵒᵖ`, so the
      -- restriction functor is `𝟙`.  Hence its action on objects is just
      -- the identity, allowing us to take `𝟙 _` here.
      simpa using (𝟙 A.2)

/-- Composition of morphisms. -/
@[simp] def comp {A B C : TotalObj} (f : Hom A B) (g : Hom B C) :
      Hom A C where
    t_le := Nat.le_trans f.t_le g.t_le
    α := (Stack.F_prod.map (Opposite.op f.t_le)).map g.α ≫ f.α

/-- Proofs of the category laws rely on functoriality of `F_prod`. -/
@[simp] lemma id_comp {A B : TotalObj} (f : Hom A B) :
      comp (id A) f = f := by
    -- destruct `f` to expose fields
    cases f with
    | mk t_le α =>
      -- time component reduction
      simp [id, comp] at *

@[simp] lemma comp_id {A B : TotalObj} (f : Hom A B) :
      comp f (id B) = f := by
    cases f with
    | mk t_le α =>
      simp [id, comp] at *

@[simp] lemma comp_assoc {A B C D : TotalObj}
      (f : Hom A B) (g : Hom B C) (h : Hom C D) :
      comp (comp f g) h = comp f (comp g h) := by
    -- Use associativity in the target category and functoriality of `map`.
    -- Unfold `comp` and reduce.
    cases f with
    | mk t₁ α₁ =>
       cases g with
       | mk t₂ α₂ =>
         cases h with
         | mk t₃ α₃ =>
           -- Simplify compositions step-by-step.
           simp [comp, Category.assoc, Functor.map_comp] at *

/-- Category instance for the total category. -/
instance totalCategory : Category TotalObj where
    Hom      := Hom
    id       := id
    comp     := comp
  id_comp' := by
      intro; apply id_comp
  comp_id' := by
      intro; apply comp_id
  assoc'   := by
      intro; intro; intro; apply comp_assoc


/-!
### Projection Functor to the Base Category

The usual Grothendieck construction comes with a forgetful functor
`π₀ : ∫ F → Time` that simply keeps the base component.  We include this
here because subsequent bridge and stack proofs rely on it.
-/

@[simp]
def projTime : TotalObj ⥤ Cat.of ℕ where
  obj := fun A => A.1
  map := fun {A B} f => f.t_le
  map_id := by
    intro A; rfl
  map_comp := by
    intro A B C f g; rfl

/-!
### Fibre Functor at a Fixed Block Height

For every `t : ℕ` we provide a functor from the full subcategory of
objects lying **over** `t` (i.e. whose time component *is exactly* `t`)
to the fibre category `F t`.

This gives a convenient way to "forget the base" once we know we are in
the designated fibre.
-/

variable (t : ℕ)

open CategoryTheory.ObjectProperty

/-- Predicate picking out objects whose time is exactly `t`. -/
def timeEq : ObjectProperty TotalObj := fun A => A.1 = t

@[simp]
lemma timeEq_holds {A : TotalObj} (h : (timeEq t) A) : A.1 = t := h

/-- The full subcategory of objects lying over the block height `t`. -/
abbrev FibreSub := (timeEq t).FullSubcategory

/-- Functor projecting a fibre object back to the underlying object in
`F_prod` over `t`. -/
@[simp]
def fibreFunctor : FibreSub t ⥤ Stack.F_prod.obj (Opposite.op t) where
  obj := fun X => by
    -- `X.obj` is a `TotalObj`; use the proof that its time is `t` to cast
    cases X with
    | mk A h =>
      simpa [timeEq] using (Eq.recOn h.symm A.2)
  map := by
    intro X Y f
    cases X with
    | mk A hA =>
      cases Y with
      | mk B hB =>
        -- `f` is a `Hom` whose `t_le` is necessarily `le_rfl`.
        let fα := f.α
        -- Coerce via the equalities to live in the right hom-set.
        simpa [timeEq] using fα
  map_id := by
    intro X
    cases X with
    | mk A hA =>
      simp [timeEq] at *
  map_comp := by
    intro X Y Z f g
    cases X with
    | mk A hA =>
      cases Y with
      | mk B hB =>
        cases Z with
        | mk C hC =>
          simp [timeEq, Category.assoc] at *

end Grothendieck 