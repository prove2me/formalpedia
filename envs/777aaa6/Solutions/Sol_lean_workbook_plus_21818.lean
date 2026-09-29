-- Prove2me | solution 1 for lean_workbook_plus_21818
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:01.362519+00:00
-- url     : https://prove2.me/submissions/da5822df-7470-41cc-a1a7-257560d44642

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 6 * (a ^ 2 + b ^ 2 + c ^ 2) + a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 + 27 ≥ 16 * (a + b + c) := by
  intros
  
  have h_identity : (6 * (a ^ 2 + b ^ 2 + c ^ 2) + a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 + 27) - (16 * (a + b + c)) = (27 : ℝ) * 1 * ((1 + ((-8 / 27) * a) + ((-8 / 27) * b) + ((-8 / 27) * c) + ((-1 / 27) * a * b) + ((-1 / 27) * a * c) + ((-1 / 27) * b * c)))^2 + ((98 / 27) : ℝ) * 1 * ((a + ((-37 / 98) * b) + ((-37 / 98) * c) + ((-4 / 49) * a * b) + ((-4 / 49) * a * c) + ((-4 / 49) * b * c)))^2 + ((46 / 49) : ℝ) * 1 * ((((-10 / 23) * b) + ((-10 / 23) * c) + (a * b) + ((-3 / 46) * a * c) + ((-3 / 46) * b * c)))^2 + ((43 / 46) : ℝ) * 1 * ((((-20 / 43) * b) + ((-20 / 43) * c) + (a * c) + ((-3 / 43) * b * c)))^2 + ((235 / 86) : ℝ) * 1 * ((b + ((-39 / 47) * c) + ((-8 / 47) * b * c)))^2 + ((40 / 47) : ℝ) * 1 * ((((-1) * c) + (b * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (6 * (a ^ 2 + b ^ 2 + c ^ 2) + a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 + 27) - (16 * (a + b + c)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
