-- Prove2me | solution 1 for lean_workbook_plus_30042
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:40:23.861422+00:00
-- url     : https://prove2.me/submissions/7a949f40-ccab-4166-b58f-aa8c2d869047

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℤ) (hx : x = 2011 ^ 16) (hy : y = 2) : x^4 + 4*y^4 = (x^2 + 2*y^2 - 2*x*y) * (x^2 + 2*y^2 + 2*x*y) := by
  (intros; simp_all)
