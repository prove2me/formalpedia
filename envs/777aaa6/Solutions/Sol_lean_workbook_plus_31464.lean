-- Prove2me | solution 1 for lean_workbook_plus_31464
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:47.157955+00:00
-- url     : https://prove2.me/submissions/f6722ca7-bb0d-4b44-ab46-c643f26fc0cf

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b > 0) (hbc : b + c > 0) (hca : a + c > 0) : a^3 + b^3 + c^3 + 3 * a * b * c ≥ a * b * (a + b) + b * c * (b + c) + c * a * (c + a) + (a * b * (a - b)^2 + b * c * (b - c)^2 + c * a * (c - a)^2) / (a + b + c) := by
  clear hab hbc hca
  by_cases hs : a+b+c = 0
  · have hza : a = 0 := by linarith
    have hzb : b = 0 := by linarith
    have hzc : c = 0 := by linarith
    simp [hza, hzb, hzc]
  have hpos : 0 < a+b+c := by rcases lt_or_gt_of_ne hs with h | h <;> linarith
  intros
  
  have h_identity : ((a ^ 4) + (b ^ 4) + (c ^ 4) + ((-1) * a * (b ^ 3)) + ((-1) * a * (c ^ 3)) + ((-1) * b * (a ^ 3)) + ((-1) * b * (c ^ 3)) + ((-1) * c * (a ^ 3)) + ((-1) * c * (b ^ 3)) + (a * b * (c ^ 2)) + (a * c * (b ^ 2)) + (b * c * (a ^ 2))) = (1 : ℝ) * 1 * (((a ^ 2) + ((-1 / 2) * (b ^ 2)) + ((-1 / 2) * (c ^ 2)) + (b * c) + ((-1 / 2) * a * b) + ((-1 / 2) * a * c)))^2 + ((3 / 4) : ℝ) * 1 * (((c ^ 2) + ((-1) * (b ^ 2)) + (a * b) + ((-1) * a * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a ^ 4) + (b ^ 4) + (c ^ 4) + ((-1) * a * (b ^ 3)) + ((-1) * a * (c ^ 3)) + ((-1) * b * (a ^ 3)) + ((-1) * b * (c ^ 3)) + ((-1) * c * (a ^ 3)) + ((-1) * c * (b ^ 3)) + (a * b * (c ^ 2)) + (a * c * (b ^ 2)) + (b * c * (a ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (a + b + c) := by positivity
  have h_rational : (a^3 + b^3 + c^3 + 3 * a * b * c) - (a * b * (a + b) + b * c * (b + c) + c * a * (c + a) + (a * b * (a - b)^2 + b * c * (b - c)^2 + c * a * (c - a)^2) / (a + b + c)) = (((a ^ 4) + (b ^ 4) + (c ^ 4) + ((-1) * a * (b ^ 3)) + ((-1) * a * (c ^ 3)) + ((-1) * b * (a ^ 3)) + ((-1) * b * (c ^ 3)) + ((-1) * c * (a ^ 3)) + ((-1) * c * (b ^ 3)) + (a * b * (c ^ 2)) + (a * c * (b ^ 2)) + (b * c * (a ^ 2)))) / ((a + b + c)) := by
    field_simp (disch := first | positivity | nlinarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
