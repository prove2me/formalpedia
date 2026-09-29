-- Prove2me | solution 1 for lean_workbook_plus_1031
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:04:32.027472+00:00
-- url     : https://prove2.me/submissions/00c8f340-113a-4edb-94c2-3260d0c7e728

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ) (hx : x > 0) : x + 1 / x ≥ 2 := by
  intros
  
  have h_identity : (1 + (x ^ 2) + ((-2) * x)) = (1 : ℝ) * 1 * ((1 + ((-1) * x)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (1 + (x ^ 2) + ((-2) * x)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < x := by positivity
  have h_rational : (x + 1 / x) - (2) = ((1 + (x ^ 2) + ((-2) * x))) / (x) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
