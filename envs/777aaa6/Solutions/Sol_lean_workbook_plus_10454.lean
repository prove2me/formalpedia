-- Prove2me | solution 1 for lean_workbook_plus_10454
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:40:50.300053+00:00
-- url     : https://prove2.me/submissions/60ef7c82-1bcd-4955-b528-d02af10f036a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : 0 < x) : Real.sqrt (x ^ 2 + 1) < x + 1 := by
  (intros; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ x ^ 2 + 1 by positivity), Real.sqrt_nonneg (x ^ 2 + 1), sq_nonneg (x)])
