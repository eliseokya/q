/--
Lift morphisms from fibre categories into the total Grothendieck category.
This allows protocol actions compiled to traces to become morphisms in ∫F.
-/

import Grothendieck.Construction
import Stack.Fibre
import Chain

namespace Stack

open Grothendieck CategoryTheory

/-- Lift a morphism in a fibre category to the total category. 
For now we assume the time component doesn't change (same block). -/
def liftMorphism {L : Chain} {t : ℕ} 
    (f : @Quiver.Hom (FibreCat L t) _ Address.default Address.default) :
    @Quiver.Hom TotalObj _ 
      ⟨t, fun _ => Address.default⟩ 
      ⟨t, fun _ => Address.default⟩ := by
  -- Build a morphism in the total category
  refine { t_le := le_refl, α := ?_ }
  -- The fibre morphism: we need to transport f through the identity functor
  simp only [F_prod, Functor.map_id]
  -- f lives in the L component of the product
  intro L'
  by_cases h : L' = L
  · cases h
    exact f
  · -- Different chain: use identity
    exact 𝟙 _

/-- Lifted identity is identity. -/
@[simp]
lemma liftMorphism_id {L : Chain} {t : ℕ} :
    liftMorphism (L:=L) (t:=t) (𝟙 Address.default) = 
    id ⟨t, fun _ => Address.default⟩ := by
  ext
  · rfl
  · intro L'
    by_cases h : L' = L <;> simp [liftMorphism, h]

end Stack 