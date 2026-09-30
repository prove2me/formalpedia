-- Prove2me | solution 1 for lean_workbook_plus_75641
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:16:41.618052+00:00
-- url     : https://prove2.me/submissions/ea63bdb1-2a99-425b-958d-244e2a245e43

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (h : a * b * c = 1) :
    1 / (a ^ 2 - a + 1) ≤ (3 / 2) * (a ^ 2 + 1) / (a ^ 4 + a ^ 2 + 1) := by
  have hd : 0 < a ^ 2 - a + 1 := by nlinarith [sq_nonneg (a - 1 / 2)]
  have he : 0 < a ^ 4 + a ^ 2 + 1 := by positivity
  apply (div_le_div_iff₀ hd he).mpr
  nlinarith [mul_nonneg hd.le (sq_nonneg (a - 1))]

#print axioms solution
