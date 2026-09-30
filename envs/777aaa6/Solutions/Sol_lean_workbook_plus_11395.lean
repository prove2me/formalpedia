-- Prove2me | solution 1 for lean_workbook_plus_11395
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:41:44.38295+00:00
-- url     : https://prove2.me/submissions/961fbd08-83ad-4d9d-99ed-68b4b50fa1a5

import Mathlib.Analysis.Complex.Basic

theorem solution {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : 1 / a + 1 / b + 1 / c ≥ 9 / (a + b + c) := by
  rw [ge_iff_le, div_add_div _ _ (ne_of_gt ha) (ne_of_gt hb),
    div_add_div _ _ (by positivity) (ne_of_gt hc),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg ha.le (sq_nonneg (b - c)), mul_nonneg hb.le (sq_nonneg (a - c)),
    mul_nonneg hc.le (sq_nonneg (a - b)), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
