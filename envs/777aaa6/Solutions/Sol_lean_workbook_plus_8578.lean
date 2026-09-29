-- Prove2me | solution 1 for lean_workbook_plus_8578
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:47:03.375711+00:00
-- url     : https://prove2.me/submissions/d82cc153-fa5d-4c25-bfa1-8977c6c00078

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x y z w : ℝ) (h₁ : w^3 = 0) (h₂ : y = 1) (h₃ : z = 0) : (x - 1)^2 * (x + 1)^2 * (x^2 - x + 1) ≥ 0 := by
  clear h₁ h₂ h₃
  have hq : 0 ≤ x ^ 2 - x + 1 := by nlinarith [sq_nonneg (2 * x - 1)]
  exact mul_nonneg (mul_nonneg (sq_nonneg (x - 1)) (sq_nonneg (x + 1))) hq
