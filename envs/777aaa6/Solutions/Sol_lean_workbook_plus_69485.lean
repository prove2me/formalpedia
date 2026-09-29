-- Prove2me | solution 1 for lean_workbook_plus_69485
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:30:44.268478+00:00
-- url     : https://prove2.me/submissions/66be2341-7b75-4d6d-83b1-3f563dfed42c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℤ) (x : ℝ) : ‖(n : ℝ) • x‖ ≤ |(n : ℝ)| • ‖x‖ := by
  norm_num
