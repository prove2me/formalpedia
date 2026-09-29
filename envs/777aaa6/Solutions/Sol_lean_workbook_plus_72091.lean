-- Prove2me | solution 1 for lean_workbook_plus_72091
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:20:11.854633+00:00
-- url     : https://prove2.me/submissions/b30dfa19-a28f-4b14-aaa6-176e1ceb583c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : x^2 + y^2 - x*y = 75) : 5*x^2 + 5*y^2 - 8*x*y ≥ 150 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
