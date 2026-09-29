-- Prove2me | solution 1 for lean_workbook_plus_41989
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:23.243214+00:00
-- url     : https://prove2.me/submissions/31c9af8b-c7f8-405f-9779-e02039bf0d55

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : a^3 * b + a^2 * b * c + c^2 * a * b ≥ 3 * a^2 * b * c := by
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have hpos_b : (0 : ℝ) ≤ b := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (a^3 * b + a^2 * b * c + c^2 * a * b) - (3 * a^2 * b * c) := by
    calc
      0 ≤ (1 : ℝ) * ((a * b)) * ((a + ((-1) * c)))^2 := by positivity
      _ = (a^3 * b + a^2 * b * c + c^2 * a * b) - (3 * a^2 * b * c) := by ring
  exact sub_nonneg.mp h
