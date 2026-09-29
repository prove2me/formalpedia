-- Prove2me | solution 1 for lean_workbook_plus_45152
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:49:49.726473+00:00
-- url     : https://prove2.me/submissions/27eb3185-e849-402b-9a9b-a97f6ea18a8a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (h₁ : a * 0 ^ 3 + b * 0 ^ 2 + c * 0 + d = 1) (h₂ : a * 1 ^ 3 + b * 1 ^ 2 + c * 1 + d = 2) (h₃ : a * 2 ^ 3 + b * 2 ^ 2 + c * 2 + d = 4) (h₄ : a * 3 ^ 3 + b * 3 ^ 2 + c * 3 + d = 8) : a * 4 ^ 3 + b * 4 ^ 2 + c * 4 + d = 15 := by
  (intros; linarith)
