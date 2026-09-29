-- Prove2me | solution 1 for lean_workbook_plus_77846
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:02:53.032566+00:00
-- url     : https://prove2.me/submissions/f14d671c-673e-44c1-ac9c-c3e025233bc1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h₁ : a * 0 ^ 2 + b * 0 + c = -2) (h₂ : a * 4 ^ 2 + b * 4 + c = 0) (h₃ : a * 6 ^ 2 + b * 6 + c = -2) : a + b + c = -3 / 4 := by
  (intros; linarith)
