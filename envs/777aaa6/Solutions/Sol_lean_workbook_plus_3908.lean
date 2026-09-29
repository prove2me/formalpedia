-- Prove2me | solution 1 for lean_workbook_plus_3908
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:15:49.666155+00:00
-- url     : https://prove2.me/submissions/50382367-6201-41a6-8e8e-c5da3931fa80

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : 1 ≤ x ∧ x ≤ 2) : x^2 ≤ 3*x - 2 := by
  (intros; nlinarith [sq_nonneg (x)])
