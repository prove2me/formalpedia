-- Prove2me | solution 1 for lean_workbook_plus_11021
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:11:55.264488+00:00
-- url     : https://prove2.me/submissions/52159c9e-d9ac-4912-91d3-6dbbbd21becb

import Mathlib.Analysis.Complex.Basic

theorem solution (p : ℝ) (hp : 3 ≤ p ∧ p < 31 / 9) (q : ℝ) (hq : q = (36 * p + 72 - p ^ 3) / (63 - 4 * p)) : p + 9 ≤ 4 * q := by
  obtain ⟨hp1, hp2⟩ := hp
  have hd : 0 < 63 - 4 * p := by linarith
  subst hq
  rw [mul_div_assoc', le_div_iff₀ hd]
  nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hp1), mul_nonneg (sub_nonneg.mpr hp1) (sub_pos.mpr hp2).le, mul_nonneg (mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hp1)) (sub_pos.mpr hp2).le]
