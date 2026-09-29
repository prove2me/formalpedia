-- Prove2me | solution 1 for lean_workbook_plus_72964
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:50:41.51586+00:00
-- url     : https://prove2.me/submissions/633cbc9b-6301-4b25-9346-c45f8c70b4c5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : 2 * x ^ 2 + 2 * y ^ 2 ≥ 4 * x * y := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
