-- Prove2me | solution 2 for lean_workbook_plus_54891
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:01:58.989656+00:00
-- url     : https://prove2.me/submissions/1067b541-6212-41b3-8907-923deda47cef

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ): (x^2 - 5*x + y^2 + x*y - 4*y + 2014) ≥ -1879 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
