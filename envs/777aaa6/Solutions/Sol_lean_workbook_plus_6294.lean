-- Prove2me | solution 1 for lean_workbook_plus_6294
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:40:23.261271+00:00
-- url     : https://prove2.me/submissions/e9fa1132-91fa-4577-afb5-409846e7eb23

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y) * (y + z) * (z + x) ≥ (8 / 9) * (x + y + z) * (x * y + y * z + z * x) := by
  nlinarith [mul_nonneg hx.le (sq_nonneg (y - z)), mul_nonneg hy.le (sq_nonneg (z - x)),
    mul_nonneg hz.le (sq_nonneg (x - y))]
