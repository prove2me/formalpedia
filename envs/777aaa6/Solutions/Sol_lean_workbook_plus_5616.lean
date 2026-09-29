-- Prove2me | solution 1 for lean_workbook_plus_5616
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:16:47.341795+00:00
-- url     : https://prove2.me/submissions/c34b98a2-a77d-4828-91a1-135d089a412e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (1 / (x * y * z)) ≥ 9 / ((x * y + y * z + x * z) * (x + y + z)) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
