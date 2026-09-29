-- Prove2me | solution 1 for lean_workbook_plus_37458
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:53:43.472089+00:00
-- url     : https://prove2.me/submissions/42eab0c2-5832-4170-b8c9-2de3b2da232f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x^2 + y^2 + z^2 + 3 * x * y - x * z - y * z ≥ 4 * x * y := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
