import Time.Category
import Stack.Presheaf
import Chain
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Functor

/-!
Global presheaf `F` defined as the (finite) product of individual chain
presheaves `F_L`.  Now uses the `Chain` enumeration instead of a generic
index type.
-/

open CategoryTheory

universe u

namespace Stack

/-- Product over all chains. Since Chain is finite, we can use a simple
Pi-type construction. -/
@[simp] def F_prod : (Time)ᵒᵖ ⥤ Cat :=
{ obj := fun t =>
    Cat.of (∀ L : Chain, (FL L).obj t),
  map := fun {t s} h =>
    { obj := fun f L => ((FL L).map h).obj (f L),
      map := fun g L => ((FL L).map h).map (g L) },
  map_id := by
    intro t; ext L; simp,
  map_comp := by
    intros; ext L; simp }

end Stack 