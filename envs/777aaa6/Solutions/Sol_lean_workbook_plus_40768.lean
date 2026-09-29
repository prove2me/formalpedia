-- Prove2me | solution 1 for lean_workbook_plus_40768
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:39:50.040733+00:00
-- url     : https://prove2.me/submissions/dfe34eb2-de68-492d-b3c8-1f297808c7d5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (f : ℝ → ℝ)
  (h₀ : x^2 - x - 1 ≠ 0)
  (h₁ : x^2 - x + 1 ≠ 0)
  (h₂ : f x = (1 - x) * (1 + x))
  (h₃ : 0 < x) :
  f x = 1 - x^2 := by
  (intros; linarith)
