-- Prove2me | solution 1 for lean_workbook_plus_17988
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:07:01.814521+00:00
-- url     : https://prove2.me/submissions/3d0bc878-81bd-433a-8f3d-087c95b4987e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution : ∀ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 → (x^2*y^2 + z^2*y^2 + x^2*z^2) / (x*y*z) ≥ x + y + z := by
  intro x y z
  intros
  have p2m_pos_x : (0 : ℝ) < x := by grind
  have p2m_pos_y : (0 : ℝ) < y := by grind
  have p2m_pos_z : (0 : ℝ) < z := by grind
  
  
  have h_identity : (((x ^ 2) * (y ^ 2)) + ((x ^ 2) * (z ^ 2)) + ((y ^ 2) * (z ^ 2)) + ((-1) * x * y * (z ^ 2)) + ((-1) * x * z * (y ^ 2)) + ((-1) * y * z * (x ^ 2))) = ((1 / 2) : ℝ) * 1 * (((x * y) + ((-1) * x * z)))^2 + ((1 / 2) : ℝ) * 1 * (((x * y) + ((-1) * y * z)))^2 + ((1 / 2) : ℝ) * 1 * (((x * z) + ((-1) * y * z)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (((x ^ 2) * (y ^ 2)) + ((x ^ 2) * (z ^ 2)) + ((y ^ 2) * (z ^ 2)) + ((-1) * x * y * (z ^ 2)) + ((-1) * x * z * (y ^ 2)) + ((-1) * y * z * (x ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (x * y * z) := by positivity
  have h_rational : ((x^2*y^2 + z^2*y^2 + x^2*z^2) / (x*y*z)) - (x + y + z) = ((((x ^ 2) * (y ^ 2)) + ((x ^ 2) * (z ^ 2)) + ((y ^ 2) * (z ^ 2)) + ((-1) * x * y * (z ^ 2)) + ((-1) * x * z * (y ^ 2)) + ((-1) * y * z * (x ^ 2)))) / ((x * y * z)) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
