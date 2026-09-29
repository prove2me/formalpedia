-- Prove2me | solution 1 for lean_workbook_plus_47670
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:51:15.660874+00:00
-- url     : https://prove2.me/submissions/2f0211b7-b79f-4c9a-ae56-4d63cbdf0a27

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : x + y + z = 5 ∧ x^2 + y^2 + z^2 = 5 ∧ x^3 + y^3 + z^3 = 5) : x^5 + y^5 + z^5 = 125 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
