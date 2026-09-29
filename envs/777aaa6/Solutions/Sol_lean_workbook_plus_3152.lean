-- Prove2me | solution 1 for lean_workbook_plus_3152
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:06:20.404319+00:00
-- url     : https://prove2.me/submissions/dbd5254a-e6a6-45f4-8c0d-ddaf7f5fa4a6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1) : x / (2 * x + y) + y / (x + 3 * y) ≤ 3 / 5 := by
  intros
  
  have h_identity : ((x ^ 2) + (4 * (y ^ 2)) + ((-4) * x * y)) = (1 : ℝ) * 1 * ((x + ((-2) * y)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((x ^ 2) + (4 * (y ^ 2)) + ((-4) * x * y)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (5 * (x + (3 * y)) * (y + (2 * x))) := by positivity
  have h_rational : (3 / 5) - (x / (2 * x + y) + y / (x + 3 * y)) = (((x ^ 2) + (4 * (y ^ 2)) + ((-4) * x * y))) / ((5 * (x + (3 * y)) * (y + (2 * x)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
