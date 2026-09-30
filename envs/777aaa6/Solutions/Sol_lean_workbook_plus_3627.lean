-- Prove2me | solution 1 for lean_workbook_plus_3627
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:14:16.489903+00:00
-- url     : https://prove2.me/submissions/199f08c7-59fb-4031-9f29-4ed62c0d3dbb

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) : (|a + b| / (1 + |a + b|)) ≤ (|a| / (1 + |a|)) + (|b| / (1 + |b|)) := by
  have hs : 0 ≤ |a + b| := abs_nonneg _
  have hp : 0 ≤ |a| := abs_nonneg _
  have hq : 0 ≤ |b| := abs_nonneg _
  have htri : |a + b| ≤ |a| + |b| := abs_add_le _ _
  rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg hp hq, mul_nonneg (mul_nonneg hp hq) hs, mul_nonneg hp hs, mul_nonneg hq hs]
