-- Prove2me | solution 1 for lean_workbook_plus_71556
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:51:49.538748+00:00
-- url     : https://prove2.me/submissions/b85a71f6-3289-4450-9ad4-c1026845bbc0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : x + y + z = 0) :
  x^3 + y^3 + z^3 = 3 * x * y * z := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
