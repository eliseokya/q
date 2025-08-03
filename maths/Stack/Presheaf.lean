import Time.Category
import Stack.Fibre
import Chain
import Mathlib.CategoryTheory.Functor

/-!
Single-chain presheaf `F_L : Timeᵒᵖ ⥤ Cat`.
Now uses the actual `FibreCat` which will eventually contain
EVM traces, but for now is still a placeholder category.
-/

open CategoryTheory

namespace Stack

/-- Chain presheaf mapping block heights to the fibre category at that height. -/
@[simp]
def FL (L : Chain) : (Time)ᵒᵖ ⥤ Cat where
  obj t := Cat.of (FibreCat L (unop t))
  map {t s} h := 𝟙 _  -- identity functor between fibres
  map_id := by intros; simp
  map_comp := by intros; simp

end Stack 