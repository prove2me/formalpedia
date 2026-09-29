-- Prove2me | solution 1 for lean_workbook_plus_23935
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:49:24.245353+00:00
-- url     : https://prove2.me/submissions/3737cc10-75d1-47c3-8c27-c199f3427bc9

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x₁ x₂ x₃ : ℝ) (h : x₁ + x₂ + x₃ = 0) :
  x₁ * x₂ * x₃ ≥ x₁ * x₂ + x₂ * x₃ + x₃ * x₁ - (x₁ * x₂ + x₂ * x₃ + x₃ * x₁)^2 := by
  have hx : x₃ = -x₁-x₂ := by linarith
  subst x₃
  nlinarith only [sq_nonneg (x₁*x₂-(x₁+x₂)/2), mul_nonneg (sq_nonneg (x₁+x₂)) (add_nonneg (sq_nonneg x₁) (sq_nonneg x₂)), sq_nonneg (x₁+x₂), sq_nonneg x₁, sq_nonneg x₂]
