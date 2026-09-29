-- Prove2me | solution 1 for lean_workbook_plus_3308
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:08:42.164269+00:00
-- url     : https://prove2.me/submissions/35378be9-dc31-4928-9a87-aba26ffa2515

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : x + y + z = 0) : x^3 + y^3 + z^3 - 3*x*y*z = 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
