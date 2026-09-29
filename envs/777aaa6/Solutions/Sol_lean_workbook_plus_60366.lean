-- Prove2me | solution 1 for lean_workbook_plus_60366
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:33:00.518427+00:00
-- url     : https://prove2.me/submissions/56a7ea8e-aaac-498c-95d9-5eb913490c19

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (z : ℂ) (a : ℝ) : ‖z‖ = a → ‖1/z‖ = 1/a := by
  norm_num
