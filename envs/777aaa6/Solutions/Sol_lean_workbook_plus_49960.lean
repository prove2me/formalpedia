-- Prove2me | solution 1 for lean_workbook_plus_49960
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:21:19.567526+00:00
-- url     : https://prove2.me/submissions/c088e528-b322-4546-8dc3-d8e33af0fab4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : x + y + z = 13) :
 √(x^2 + y^2 + z^2) >= 5 := by
  (intros; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ x^2 + y^2 + z^2 by positivity), Real.sqrt_nonneg (x^2 + y^2 + z^2), sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
