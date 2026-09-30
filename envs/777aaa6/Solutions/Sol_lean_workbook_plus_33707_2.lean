-- Prove2me | solution 2 for lean_workbook_plus_33707
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:15:21.41641+00:00
-- url     : https://prove2.me/submissions/d442d8ea-4955-4116-80e0-ad11c8881329

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : 0 < x ∧ x < 1) :
  ∃ y, ∑' n : ℕ, (n^2 * x^(2 * n)) = y := by
  norm_num
