-- Prove2me | solution 1 for lean_workbook_plus_68819
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:50:12.218219+00:00
-- url     : https://prove2.me/submissions/43bb445d-d3de-43ba-8a6a-71b6e695c120

import Mathlib

namespace ShiftedCubicSharpPositiveMinimum

noncomputable def criticalOffset : ℝ := Real.sqrt 3 / 3

theorem offset_pos : 0 < criticalOffset := by
  unfold criticalOffset
  positivity

theorem offset_sq : criticalOffset ^ 2 = 1 / 3 := by
  unfold criticalOffset
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem minimum_pos : 0 < 1 - 4 * Real.sqrt 3 / 9 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hp := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

theorem gap_identity (p : ℝ) :
    (2 * p ^ 3 + 4 * p + 1 - 6 * p ^ 2) - (1 - 4 * Real.sqrt 3 / 9) =
      2 * (p - 1 - criticalOffset) ^ 2 * (p - 1 + 2 * criticalOffset) := by
  have hs := offset_sq
  unfold criticalOffset at hs ⊢
  linear_combination (6 * (p - 1) - 4 * (Real.sqrt 3 / 3)) * hs

theorem sharp_bound (p : ℝ) (hp : 1 ≤ p) :
    1 - 4 * Real.sqrt 3 / 9 ≤ 2 * p ^ 3 + 4 * p + 1 - 6 * p ^ 2 := by
  have hf : 0 ≤ p - 1 + 2 * criticalOffset := by linarith [offset_pos]
  have h := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (sq_nonneg (p - 1 - criticalOffset))) hf
  linarith [gap_identity p]

theorem equality_iff (p : ℝ) (hp : 1 ≤ p) :
    2 * p ^ 3 + 4 * p + 1 - 6 * p ^ 2 = 1 - 4 * Real.sqrt 3 / 9 ↔
      p = 1 + Real.sqrt 3 / 3 := by
  constructor
  · intro h
    have hf : 0 < p - 1 + 2 * criticalOffset := by linarith [offset_pos]
    have hz : 2 * (p - 1 - criticalOffset) ^ 2 *
        (p - 1 + 2 * criticalOffset) = 0 := by linarith [gap_identity p]
    have ht := (mul_eq_zero.mp hz).resolve_right (ne_of_gt hf)
    have hs := (mul_eq_zero.mp ht).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
    have he := (sq_eq_zero_iff).mp hs
    unfold criticalOffset at he
    linarith
  · intro h
    have he : p - 1 - criticalOffset = 0 := by
      unfold criticalOffset
      linarith
    have hi := gap_identity p
    rw [he, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_mul] at hi
    linarith

theorem attained_minimum :
    ∃ p : ℝ, 1 ≤ p ∧
      2 * p ^ 3 + 4 * p + 1 - 6 * p ^ 2 = 1 - 4 * Real.sqrt 3 / 9 := by
  have hp : (1 : ℝ) ≤ 1 + Real.sqrt 3 / 3 := by
    linarith [Real.sqrt_nonneg (3 : ℝ)]
  exact ⟨1 + Real.sqrt 3 / 3, hp, (equality_iff _ hp).mpr rfl⟩

theorem strict_bound (p : ℝ) (hp : 1 ≤ p) :
    6 * p ^ 2 < 2 * p ^ 3 + 4 * p + 1 := by
  linarith [sharp_bound p hp, minimum_pos]

end ShiftedCubicSharpPositiveMinimum

theorem solution (p : ℝ) (h₀ : 1 ≤ p) :
    2 * p ^ 3 + 4 * p + 1 ≥ 6 * p ^ 2 :=
  (ShiftedCubicSharpPositiveMinimum.strict_bound p h₀).le

#print axioms ShiftedCubicSharpPositiveMinimum.minimum_pos
#print axioms ShiftedCubicSharpPositiveMinimum.gap_identity
#print axioms ShiftedCubicSharpPositiveMinimum.sharp_bound
#print axioms ShiftedCubicSharpPositiveMinimum.equality_iff
#print axioms ShiftedCubicSharpPositiveMinimum.attained_minimum
#print axioms ShiftedCubicSharpPositiveMinimum.strict_bound
#print axioms solution
