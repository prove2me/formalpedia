-- Prove2me | solution 1 for lean_workbook_plus_42652
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:16:54.9635+00:00
-- url     : https://prove2.me/submissions/f59b2f6f-ce91-430b-938c-3e45f136da5f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : (x ^ 2 + y ^ 2) / 2 ≥ Real.sqrt (x ^ 2 * y ^ 2) := by
  (intros; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ x ^ 2 * y ^ 2 by positivity), Real.sqrt_nonneg (x ^ 2 * y ^ 2), sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
