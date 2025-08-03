import Mathlib
import Protocol.Compound.Step

namespace Compound.Alg

open Compound

@[simp] lemma one_plus_r_pos : (0 : ℚ) < 1 + r := by
  have : (r : ℚ) = 1/10 := by rfl
  norm_num [r]

lemma pos_pow {n : Nat} : (0 : ℚ) < (1 + r) ^ n := by
  have hp : (0 : ℚ) < 1 + r := one_plus_r_pos
  have hne : (1 + r : ℚ) ≠ 0 := by exact ne_of_gt hp
  induction n with
  | zero => simp
  | succ n ih =>
      simpa using mul_pos hp ih

/-- If borrow is within margin `k`, one accrue step preserves health with margin exponent decreased by 1. -/
lemma accrue_preserve_margin {s b : ℚ} {k : Nat}
    (h : s ≥ (1 + r) ^ (k.succ) * b) :
    s ≥ (1 + r) ^ k * ((1 + r) * b) := by
  have hp : (0 : ℚ) < (1 + r) ^ k := pos_pow k
  have hmul : (1 + r) ^ (k.succ) = (1 + r) ^ k * (1 + r) := by
    simp [pow_succ]
  have : s ≥ (1 + r) ^ k * (1 + r) * b := by
    simpa [hmul, mul_comm, mul_left_comm] using h
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

lemma margin_implies_healthy {s b : ℚ} {k : Nat}
    (h : s ≥ (1 + r) ^ k * b) (hb : 0 ≤ b) : s ≥ b :=
by
  have hp : 0 < (1 + r) ^ k := pos_pow k
  have : (1 + r) ^ k * b ≤ s := by
    linarith
  have hpos : 0 < (1 + r) ^ k := hp
  have hscale := (div_le_iff hpos).mpr this
  simpa [div_eq_mul_inv] using hscale

lemma margin_stable_supply {s b a : ℚ} {k : Nat}
    (hinv : s ≥ (1 + r) ^ k * b) (ha : 0 ≤ a) :
    s + a ≥ (1 + r) ^ k * b := by
  linarith

lemma margin_stable_repay {s b a : ℚ} {k : Nat}
    (hinv : s ≥ (1 + r) ^ k * b) (ha : 0 ≤ a) :
    s ≥ (1 + r) ^ k * max 0 (b - a) := by
  have hmax : max 0 (b - a) ≤ b := max_le_left _ _
  have hscale : (1 + r) ^ k * max 0 (b - a) ≤ (1 + r) ^ k * b :=
    mul_le_mul_of_nonneg_left hmax (le_of_lt (pos_pow k))
  exact le_trans hscale hinv

open Compound.Prim

/-- Count the number of `accrue` operations in an `Action` list. -/
@[simp] def accCount : List Prim → Nat
  | [] => 0
  | accrue :: tl => accCount tl + 1
  | _ :: tl => accCount tl

/-- Tail decomposition lemma for `accCount`. -/
lemma accCount_cons (p : Prim) (tl : List Prim) :
    accCount (p :: tl) = accCount tl + (if p = accrue then 1 else 0) := by
  cases p with
  | accrue => simp [accCount]
  | supply a => simp [accCount]
  | repay a  => simp [accCount]

/-- Margin transformation for one primitive action. Returns the *new* exponent.
If the action is `accrue`, the exponent decreases by 1; otherwise it stays the same. -/
lemma margin_after_one
    (p : Prim) (s b : ℚ) {k : Nat}
    (hinv : s ≥ (1 + r) ^ k * b) (hb : 0 ≤ b) :
    let l' := applyPrim p { s := s, b := b };
    ∃ k', l'.s ≥ (1 + r) ^ k' * l'.b ∧ k' ≤ k := by
  cases p with
  | accrue =>
      -- debt increases by (1+r)
      have h1 : s ≥ (1 + r) ^ k.succ * b := by
        simpa [pow_succ] using hinv
      have h2 : s ≥ (1 + r) ^ k * ((1 + r) * b) :=
        accrue_preserve_margin (s:=s) (b:=b) (k:=k) h1
      refine ?_
      let l' := applyPrim Prim.accrue {s:=s, b:=b}
      have : l' = { s := s, b := (1 + r) * b } := by simp [applyPrim]
      refine ⟨k, ?_, Nat.le_refl _⟩
      simpa [this] using h2
  | supply a =>
      have hS : s + a ≥ (1 + r) ^ k * b :=
        margin_stable_supply (k:=k) hinv (ha:=by linarith)
      refine ?_
      let l' := applyPrim (Prim.supply a) {s:=s, b:=b}
      have : l' = { s := s + a, b := b } := by simp [applyPrim]
      refine ⟨k, ?_, le_rfl⟩
      simpa [this] using hS
  | repay a =>
      have hS : s ≥ (1 + r) ^ k * max 0 (b - a) :=
        margin_stable_repay (k:=k) hinv (ha:=by linarith)
      refine ?_
      let l' := applyPrim (Prim.repay a) {s:=s, b:=b}
      have : l' = { s := s, b := max 0 (b - a) } := by simp [applyPrim]
      refine ⟨k, ?_, le_rfl⟩
      simpa [this] using hS

end Compound.Alg 