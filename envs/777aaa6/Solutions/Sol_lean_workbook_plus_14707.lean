-- Prove2me | solution 1 for lean_workbook_plus_14707
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:38:53.39105+00:00
-- url     : https://prove2.me/submissions/3f632d8e-adc2-4eed-8db3-82ab3abf9c15

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : x^2 - 4 * x * y - y^2 ≤ 3 * x^2 + y^2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
