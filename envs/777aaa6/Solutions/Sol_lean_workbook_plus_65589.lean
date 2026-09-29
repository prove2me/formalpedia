-- Prove2me | solution 1 for lean_workbook_plus_65589
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:48:22.833261+00:00
-- url     : https://prove2.me/submissions/f2fb40ce-0a4c-4b24-b387-978f02ede854

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x₁ x₂ x₃ a b : ℝ) (h₁ : x₁ + x₂ = -a) (h₂ : x₂ + x₃ = -b) : x₁ - x₃ = b - a := by
  (intros; linarith)
