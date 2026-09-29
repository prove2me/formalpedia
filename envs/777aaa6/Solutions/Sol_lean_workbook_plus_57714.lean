-- Prove2me | solution 1 for lean_workbook_plus_57714
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:45:55.029779+00:00
-- url     : https://prove2.me/submissions/d2886c8b-8a99-4ed3-b203-147d3f9e312b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℕ) (μ : ℝ) (θ : ℝ) (T₁ : ℝ) : ∃ T₂, T₂ = T₁ * (1 + μ * θ / n)^n := by
  norm_num
