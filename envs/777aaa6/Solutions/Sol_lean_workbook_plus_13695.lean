-- Prove2me | solution 1 for lean_workbook_plus_13695
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:23:10.963803+00:00
-- url     : https://prove2.me/submissions/346bd7e5-ec32-4c64-9866-f76998fbe8b7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ)
  (h₀ : x + y = 7)
  (h₁ : x^2 - y^2 = 21)
  (h₂ : y = 7 - x)
  (h₃ : x^2 - (7 - x)^2 = 21) :
  2 * x + 3 * y = 16 := by
  (intros; linarith)
