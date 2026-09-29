-- Prove2me | solution 1 for lean_workbook_plus_42964
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:37.321361+00:00
-- url     : https://prove2.me/submissions/2cbe6d2c-063d-4412-89e2-bdf58b0a219c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y : ℝ)
    (a b : ℝ)
    (h₀ : x = a^2 + b^2)
    (h₁ : y = a * b) :
    (x - 2 * y)^2 * (17 * x^2 + 4 * x * y + 4 * y^2) ≥ 0 := by
  intros
  
  have h_identity : ((x - 2 * y)^2 * (17 * x^2 + 4 * x * y + 4 * y^2)) - (0) = (17 : ℝ) * 1 * (((x ^ 2) + ((-4 / 17) * (y ^ 2)) + ((-32 / 17) * x * y)))^2 + ((64 / 17) : ℝ) * 1 * ((((-2) * (y ^ 2)) + (x * y)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((x - 2 * y)^2 * (17 * x^2 + 4 * x * y + 4 * y^2)) - (0) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
