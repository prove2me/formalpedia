-- Prove2me | solution 1 for lean_workbook_plus_3940
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:15:32.790918+00:00
-- url     : https://prove2.me/submissions/c59177b9-f0cb-4acc-bc43-3a429c247911

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : x + y + z = x*y*z) :
  x * (1 - y ^ 2) * (1 - z ^ 2) + y * (1 - z ^ 2) * (1 - x ^ 2) + z * (1 - x ^ 2) * (1 - y ^ 2) = 4*x*y*z := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
