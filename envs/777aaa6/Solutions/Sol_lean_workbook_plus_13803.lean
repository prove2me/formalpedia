-- Prove2me | solution 1 for lean_workbook_plus_13803
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:23:24.355717+00:00
-- url     : https://prove2.me/submissions/bfeed760-3d06-4913-ba52-eaa0c32a315f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : -3 < x ∧ x < 3) (n : ℕ) : ∃ y, ∑' n : ℕ, (x^n / (3^n * n^2)) = y := by
  norm_num
