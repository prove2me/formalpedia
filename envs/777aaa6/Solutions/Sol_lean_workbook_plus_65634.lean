-- Prove2me | solution 1 for lean_workbook_plus_65634
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:41:18.969556+00:00
-- url     : https://prove2.me/submissions/11deec86-527c-492c-a780-fa38554d5768

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : 2 + 2 * (a ^ 4 + b ^ 4) ≥ a * b ^ 3 + b * a ^ 3 + a ^ 3 + b ^ 3 + a + b := by
  intros
  
  have h : (0 : ℝ) ≤ (2 + 2 * (a ^ 4 + b ^ 4)) - (a * b ^ 3 + b * a ^ 3 + a ^ 3 + b ^ 3 + a + b) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * (1) * ((1 + ((-1) * a)))^2 + ((1 / 2) : ℝ) * (1) * ((1 + ((-1) * (a ^ 2))))^2 + ((1 / 2) : ℝ) * (1) * ((1 + ((-1) * b)))^2 + ((1 / 2) : ℝ) * (1) * ((1 + ((-1) * (b ^ 2))))^2 + ((1 / 2) : ℝ) * (1) * ((a + ((-1) * (a ^ 2))))^2 + ((1 / 2) : ℝ) * (1) * (((a ^ 2) + ((-1) * a * b)))^2 + ((1 / 2) : ℝ) * (1) * (((a ^ 2) + ((-1) * (b ^ 2))))^2 + ((1 / 2) : ℝ) * (1) * ((((-1) * (b ^ 2)) + (a * b)))^2 + ((1 / 2) : ℝ) * (1) * ((b + ((-1) * (b ^ 2))))^2 := by positivity
      _ = (2 + 2 * (a ^ 4 + b ^ 4)) - (a * b ^ 3 + b * a ^ 3 + a ^ 3 + b ^ 3 + a + b) := by ring
  exact sub_nonneg.mp h
