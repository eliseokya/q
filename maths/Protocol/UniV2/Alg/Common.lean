import Mathlib

namespace UniV2.Alg

@[simp] def α : ℚ := 997/1000

lemma alpha_nonzero : (α : ℚ) ≠ 0 := by
  norm_num [α]

lemma alpha_pos : (0 : ℚ) < α := by
  norm_num [α]

end UniV2.Alg 