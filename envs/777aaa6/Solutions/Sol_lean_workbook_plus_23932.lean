-- Prove2me | solution 1 for lean_workbook_plus_23932
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:30:15.227811+00:00
-- url     : https://prove2.me/submissions/72a6604d-7251-4501-abfa-be740ec5cb36

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a + Real.sqrt (a * b) ≤ (9 / 8) * (a + b) → 1 / a + 2 / (a + b) ≤ (9 / 8) * (1 / a + 1 / b) := by
  intros
  
  have h_identity : ((b ^ 2) + (9 * (a ^ 2)) + ((-6) * a * b)) = (9 : ℝ) * 1 * ((a + ((-1 / 3) * b)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((b ^ 2) + (9 * (a ^ 2)) + ((-6) * a * b)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (8 * a * b * (a + b)) := by positivity
  have h_rational : ((9 / 8) * (1 / a + 1 / b)) - (1 / a + 2 / (a + b)) = (((b ^ 2) + (9 * (a ^ 2)) + ((-6) * a * b))) / ((8 * a * b * (a + b))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
