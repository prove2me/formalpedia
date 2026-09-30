-- Prove2me | solution 1 for lean_workbook_plus_20966
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:43:35.064689+00:00
-- url     : https://prove2.me/submissions/84433a73-a311-4a2e-9931-4bc8ba95fda1

import Mathlib.Analysis.Complex.Basic

theorem solution (a : ℝ) :
  Real.sqrt (a^2) = a ↔ 0 ≤ a := by
  rw [Real.sqrt_sq_eq_abs]
  exact abs_eq_self
