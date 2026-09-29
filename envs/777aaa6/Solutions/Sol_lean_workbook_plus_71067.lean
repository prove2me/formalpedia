-- Prove2me | solution 1 for lean_workbook_plus_71067
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:53:08.831164+00:00
-- url     : https://prove2.me/submissions/6b52970c-0471-4c29-a527-aa530e037b35

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : x^2 - 4*x*y - y^2 = 5) : 3*x^2 + y^2 ≥ 5 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
