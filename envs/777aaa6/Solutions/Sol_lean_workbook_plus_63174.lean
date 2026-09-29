-- Prove2me | solution 1 for lean_workbook_plus_63174
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:17:39.35162+00:00
-- url     : https://prove2.me/submissions/1b7b88fc-419e-4297-a835-f07d15918f13

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (n : ℕ) (h₁ : x + y = 1) (h₂ : x * y = -1) : ∃ a_n : ℝ, a_n = x^n + y^n := by
  norm_num
