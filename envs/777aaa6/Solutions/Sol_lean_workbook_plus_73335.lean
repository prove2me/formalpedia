-- Prove2me | solution 1 for lean_workbook_plus_73335
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:50:47.460029+00:00
-- url     : https://prove2.me/submissions/60f47032-f065-447c-b42a-a1bacec1093b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (a : ℝ) (h₁ : f a = 0) (h₂ : a = 0 ∨ a = 1 / 2) : a = 0 ∨ a = 1 / 2 := by
  (intros; simp_all)
