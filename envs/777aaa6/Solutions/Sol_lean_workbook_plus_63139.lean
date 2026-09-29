-- Prove2me | solution 1 for lean_workbook_plus_63139
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:17:44.98484+00:00
-- url     : https://prove2.me/submissions/cf75e46a-d21b-4e7e-8c23-c30709bb0149

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : 4 * x ^ 2 + 6 * x * y + 4 * y ^ 2 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
