-- Prove2me | solution 1 for lean_workbook_plus_27363
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:14:40.684865+00:00
-- url     : https://prove2.me/submissions/a182fab8-c700-43d6-bc9e-c2f7d9f6ef46

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a + b - 2) ^ 2 + (a + c - 2) ^ 2 + (b + c - 2) ^ 2 ≥ 0 := by
  (intros; positivity)
