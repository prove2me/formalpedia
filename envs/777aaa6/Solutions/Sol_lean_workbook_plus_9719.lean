-- Prove2me | solution 1 for lean_workbook_plus_9719
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:40:20.374906+00:00
-- url     : https://prove2.me/submissions/7b070453-5657-44ae-bee0-563624cec136

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx: 0 ≤ x ∧ x ≤ 2) (hy: 0 ≤ y ∧ y ≤ √(2 * x - x^2)) : 0 ≤ √(x^2 + y^2) := by
  norm_num
