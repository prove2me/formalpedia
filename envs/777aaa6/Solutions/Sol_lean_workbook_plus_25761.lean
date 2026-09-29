-- Prove2me | solution 1 for lean_workbook_plus_25761
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:34.150037+00:00
-- url     : https://prove2.me/submissions/74e13651-2983-4a9a-b8f0-10c53ce5780f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 1 / a + 2 / b ≥ 8 / (2 * a + b) := by
  intros
  
  have h_identity : ((b ^ 2) + (4 * (a ^ 2)) + ((-4) * a * b)) = (4 : ℝ) * 1 * ((a + ((-1 / 2) * b)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((b ^ 2) + (4 * (a ^ 2)) + ((-4) * a * b)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (a * b * (b + (2 * a))) := by positivity
  have h_rational : (1 / a + 2 / b) - (8 / (2 * a + b)) = (((b ^ 2) + (4 * (a ^ 2)) + ((-4) * a * b))) / ((a * b * (b + (2 * a)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
