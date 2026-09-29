-- Prove2me | solution 1 for lean_workbook_plus_61634
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:20:05.326304+00:00
-- url     : https://prove2.me/submissions/b93ca0bb-661c-4055-a631-51b58f606f93

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x^4 + x^2 * y^2) + (y^4 + y^2 * z^2) + (z^4 + z^2 * x^2) ≥ 2 * (x^3 * y + y^3 * z + z^3 * x) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
