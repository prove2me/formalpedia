-- Prove2me | solution 1 for lean_workbook_plus_6324
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:49:58.615228+00:00
-- url     : https://prove2.me/submissions/d2763702-3859-4c3b-b43d-7aadb0c5192b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (b : ℝ) (h₁ : y = 3 * x + b) (h₂ : x = -b / 3) : y = 0 := by
  (intros; linarith)
