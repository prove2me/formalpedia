-- Prove2me | solution 1 for lean_workbook_plus_17035
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:14:41.969134+00:00
-- url     : https://prove2.me/submissions/cb678964-a04d-4e1e-8e86-d5c320ef60c0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : x - 9*y = 0) (h₂ : 9*x - y = 0) : x + y = 0 := by
  (intros; linarith)
