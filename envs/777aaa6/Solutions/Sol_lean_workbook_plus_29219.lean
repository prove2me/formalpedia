-- Prove2me | solution 1 for lean_workbook_plus_29219
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:04:50.441287+00:00
-- url     : https://prove2.me/submissions/985e21b1-8950-4286-99e9-63ebe08fcea9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a - b) ^ 2 + (a - c) ^ 2 + (b - c) ^ 2 ≥ 0 := by
  (intros; positivity)
