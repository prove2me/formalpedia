-- Prove2me | solution 1 for lean_workbook_plus_26534
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:25:36.795376+00:00
-- url     : https://prove2.me/submissions/a4f6269a-fee6-4874-9602-ffb4ab27ad53

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : 3 * x ^ 2 + 3 * y ^ 2 + 3 * x * y + 3 * x + 3 * y + 4 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
