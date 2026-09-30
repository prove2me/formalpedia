-- Prove2me | solution 1 for lean_workbook_plus_70978
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:36:49.54793+00:00
-- url     : https://prove2.me/submissions/3a3ee5c0-e321-49fd-b6f6-bd4de4403d48

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

theorem positive_denominator_bound (a : ℝ) (hd : 0 < a ^ 3 + 4) :
    a / (a ^ 3 + 4) ≤ (2 * a + 3) / 25 := by
  apply (div_le_div_iff₀ hd (by norm_num)).mpr
  have hq : 0 ≤ 2 * a ^ 2 + 7 * a + 12 := by nlinarith [sq_nonneg (4 * a + 7)]
  have hp := mul_nonneg (sq_nonneg (a - 1)) hq
  nlinarith only [hp]

theorem sharp_equality (a : ℝ) (hd : 0 < a ^ 3 + 4) :
    a / (a ^ 3 + 4) = (2 * a + 3) / 25 ↔ a = 1 := by
  rw [div_eq_div_iff (ne_of_gt hd) (by norm_num)]
  constructor
  · intro h
    have hq : 0 < 2 * a ^ 2 + 7 * a + 12 := by nlinarith [sq_nonneg (4 * a + 7)]
    have hp : (a - 1) ^ 2 * (2 * a ^ 2 + 7 * a + 12) = 0 := by nlinarith only [h]
    have hz : (a - 1) ^ 2 = 0 := (mul_eq_zero.mp hp).resolve_right (ne_of_gt hq)
    nlinarith
  · rintro rfl
    norm_num

theorem solution (a : ℝ) (ha : 0 ≤ a) :
    a / (a ^ 3 + 4) ≤ (2 * a + 3) / 25 :=
  positive_denominator_bound a (by positivity)
