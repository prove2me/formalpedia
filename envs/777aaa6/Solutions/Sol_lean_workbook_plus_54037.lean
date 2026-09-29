-- Prove2me | solution 1 for lean_workbook_plus_54037
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:30:22.98781+00:00
-- url     : https://prove2.me/submissions/eb84e418-4cf3-489f-a9e7-0e4f12c60fd4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b s t x : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : a + b = s)
  (h₂ : a * b = t)
  (h₃ : s^2 ≥ 4 * t)
  : (x^2 + a * b)^2 * (a + b)^2 - 4 * a * b * (x^2 + a^2) * (x^2 + b^2) ≥ 0 := by
  nlinarith only [mul_nonneg (sq_nonneg (a-b)) (sq_nonneg (x^2-a*b))]
