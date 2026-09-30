-- Prove2me | solution 1 for lean_workbook_plus_238
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:22:50.656927+00:00
-- url     : https://prove2.me/submissions/043d80f7-4931-458a-bf37-65cd615b6bb2

import Mathlib

theorem solution (x_1 x_2 : ℝ) (hx_1 : 0 < x_1) (hx_2 : 0 < x_2) :
    x_1 + x_2 ≥ 2 * Real.sqrt (x_1 * x_2) := by
  have h : Real.sqrt (x_1 * x_2) ≤ (x_1 + x_2) / 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg (x_1 - x_2)]
  linarith
