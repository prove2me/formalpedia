-- Prove2me | solution 1 for lean_workbook_plus_46791
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:37:59.745297+00:00
-- url     : https://prove2.me/submissions/26d4e4cd-7ca1-43e8-b334-eaa23ff76575

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : (x - y) ^ 2 * (7 * x ^ 2 + 7 * y ^ 2 + 10 * x * y) ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
