-- Prove2me | solution 1 for lean_workbook_plus_32469
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:05:33.082796+00:00
-- url     : https://prove2.me/submissions/7829b7a3-bc7d-4dff-936c-852fb1a6b5e4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / b + b^2 / c + c^2 / a) ≥ (a^2 + b^2 + c^2) / (a * b + b * c + a * c) * (a + b + c) := by
  intros
  
  have h_identity : (((a ^ 2) * (b ^ 4)) + ((a ^ 4) * (c ^ 2)) + ((b ^ 2) * (c ^ 4)) + ((-1) * a * (b ^ 3) * (c ^ 2)) + ((-1) * b * (a ^ 2) * (c ^ 3)) + ((-1) * c * (a ^ 3) * (b ^ 2))) = ((1 / 2) : ℝ) * 1 * (((c * (a ^ 2)) + ((-1) * a * (b ^ 2))))^2 + ((1 / 2) : ℝ) * 1 * (((c * (a ^ 2)) + ((-1) * b * (c ^ 2))))^2 + ((1 / 2) : ℝ) * 1 * (((a * (b ^ 2)) + ((-1) * b * (c ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (((a ^ 2) * (b ^ 4)) + ((a ^ 4) * (c ^ 2)) + ((b ^ 2) * (c ^ 4)) + ((-1) * a * (b ^ 3) * (c ^ 2)) + ((-1) * b * (a ^ 2) * (c ^ 3)) + ((-1) * c * (a ^ 3) * (b ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (a * b * c * ((a * b) + (a * c) + (b * c))) := by positivity
  have h_rational : ((a^2 / b + b^2 / c + c^2 / a)) - ((a^2 + b^2 + c^2) / (a * b + b * c + a * c) * (a + b + c)) = ((((a ^ 2) * (b ^ 4)) + ((a ^ 4) * (c ^ 2)) + ((b ^ 2) * (c ^ 4)) + ((-1) * a * (b ^ 3) * (c ^ 2)) + ((-1) * b * (a ^ 2) * (c ^ 3)) + ((-1) * c * (a ^ 3) * (b ^ 2)))) / ((a * b * c * ((a * b) + (a * c) + (b * c)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
