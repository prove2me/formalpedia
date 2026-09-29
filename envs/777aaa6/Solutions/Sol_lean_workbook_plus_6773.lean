-- Prove2me | solution 1 for lean_workbook_plus_6773
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:17:23.023719+00:00
-- url     : https://prove2.me/submissions/885909f3-a884-41ed-928e-ee40c651a6cc

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 8 * (a^2 + 2)^2 * (b^2 + 2)^2 ≥ 81 * (a + b)^2 + 36 * a * b * (a^2 + 2) * (b^2 + 2) := by
  intros
  have h : (0 : ℝ) ≤ (8 * (a^2 + 2)^2 * (b^2 + 2)^2) - (81 * (a + b)^2 + 36 * a * b * (a^2 + 2) * (b^2 + 2)) := by
    calc
      0 ≤ (128 : ℝ) * ((1 + ((-1) * a * b)))^2 + (25 : ℝ) * ((b + ((-1) * a)))^2 + (22 : ℝ) * ((b + ((-1) * a * (b ^ 2))))^2 + (14 : ℝ) * (((b ^ 2) + ((-1) * a * b)))^2 + (18 : ℝ) * (((b ^ 2) + ((-1) * (a ^ 2))))^2 + (22 : ℝ) * ((a + ((-1) * b * (a ^ 2))))^2 + (14 : ℝ) * ((((-1) * (a ^ 2)) + (a * b)))^2 + (8 : ℝ) * (((a * b) + ((-1) * (a ^ 2) * (b ^ 2))))^2 + (10 : ℝ) * (((a * (b ^ 2)) + ((-1) * b * (a ^ 2))))^2 := by positivity
      _ = (8 * (a^2 + 2)^2 * (b^2 + 2)^2) - (81 * (a + b)^2 + 36 * a * b * (a^2 + 2) * (b^2 + 2)) := by ring
  exact sub_nonneg.mp h
