-- Prove2me | solution 1 for lean_workbook_plus_70207
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:52:38.263063+00:00
-- url     : https://prove2.me/submissions/3db43496-9c41-4f85-81a2-43793cc494d5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h₁ : a ≥ b + c) (h₂ : a = 6 - (b + c)) : a ≥ 3 := by
  (intros; linarith)
