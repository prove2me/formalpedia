-- Prove2me | solution 1 for lean_workbook_plus_11032
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:04:14.252066+00:00
-- url     : https://prove2.me/submissions/4402875a-faed-4b32-bd31-530cdae61aef

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a^2 / (b^2 + 2 * c^2) + b^2 / (c^2 + 2 * a^2) + c^2 / (a^2 + 2 * b^2)) ≥ 1 := by
  intros
  
  have h_identity : ((2 * (a ^ 6)) + (2 * (b ^ 6)) + (2 * (c ^ 6)) + ((-3) * (a ^ 2) * (b ^ 4)) + ((-3) * (a ^ 4) * (c ^ 2)) + ((-3) * (b ^ 2) * (c ^ 4)) + (2 * (a ^ 2) * (c ^ 4)) + (2 * (a ^ 4) * (b ^ 2)) + (2 * (b ^ 4) * (c ^ 2)) + ((-3) * (a ^ 2) * (b ^ 2) * (c ^ 2))) = (2 : ℝ) * 1 * ((((-1) * (b ^ 3)) + (b * (a ^ 2))))^2 + (1 : ℝ) * 1 * (((b * (a ^ 2)) + ((-1) * b * (c ^ 2))))^2 + ((1 / 2) : ℝ) * 1 * (((a ^ 3) + ((-1) * a * (b ^ 2))))^2 + ((3 / 2) : ℝ) * 1 * (((a ^ 3) + ((-1) * a * (c ^ 2))))^2 + ((1 / 2) : ℝ) * 1 * (((a * (b ^ 2)) + ((-1) * a * (c ^ 2))))^2 + (2 : ℝ) * 1 * ((((-1) * (c ^ 3)) + (c * (b ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((2 * (a ^ 6)) + (2 * (b ^ 6)) + (2 * (c ^ 6)) + ((-3) * (a ^ 2) * (b ^ 4)) + ((-3) * (a ^ 4) * (c ^ 2)) + ((-3) * (b ^ 2) * (c ^ 4)) + (2 * (a ^ 2) * (c ^ 4)) + (2 * (a ^ 4) * (b ^ 2)) + (2 * (b ^ 4) * (c ^ 2)) + ((-3) * (a ^ 2) * (b ^ 2) * (c ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (((a ^ 2) + (2 * (b ^ 2))) * ((b ^ 2) + (2 * (c ^ 2))) * ((c ^ 2) + (2 * (a ^ 2)))) := by positivity
  have h_rational : ((a^2 / (b^2 + 2 * c^2) + b^2 / (c^2 + 2 * a^2) + c^2 / (a^2 + 2 * b^2))) - (1) = (((2 * (a ^ 6)) + (2 * (b ^ 6)) + (2 * (c ^ 6)) + ((-3) * (a ^ 2) * (b ^ 4)) + ((-3) * (a ^ 4) * (c ^ 2)) + ((-3) * (b ^ 2) * (c ^ 4)) + (2 * (a ^ 2) * (c ^ 4)) + (2 * (a ^ 4) * (b ^ 2)) + (2 * (b ^ 4) * (c ^ 2)) + ((-3) * (a ^ 2) * (b ^ 2) * (c ^ 2)))) / ((((a ^ 2) + (2 * (b ^ 2))) * ((b ^ 2) + (2 * (c ^ 2))) * ((c ^ 2) + (2 * (a ^ 2))))) := by
    field_simp (disch := positivity)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
