-- Prove2me | solution 1 for lean_workbook_plus_23442
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:18:32.128441+00:00
-- url     : https://prove2.me/submissions/f9cbf006-ab37-4f84-aab4-041fa8caab5b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c d : ℝ) : -(a * c * d + a * b * d + a * b * c + b * c * d) ^ 2 + 4 * a ^ 2 * c ^ 2 * d ^ 2 + 4 * a ^ 2 * b ^ 2 * d ^ 2 + 4 * a ^ 2 * b ^ 2 * c ^ 2 + 4 * b ^ 2 * c ^ 2 * d ^ 2 ≥ 0 := by
  intros
  have h : (0 : ℝ) ≤ (-(a * c * d + a * b * d + a * b * c + b * c * d) ^ 2 + 4 * a ^ 2 * c ^ 2 * d ^ 2 + 4 * a ^ 2 * b ^ 2 * d ^ 2 + 4 * a ^ 2 * b ^ 2 * c ^ 2 + 4 * b ^ 2 * c ^ 2 * d ^ 2) - (0) := by
    calc
      0 ≤ (1 : ℝ) * (((b * c * d) + ((-1) * a * c * d)))^2 + (1 : ℝ) * (((b * c * d) + ((-1) * a * b * d)))^2 + (1 : ℝ) * (((b * c * d) + ((-1) * a * b * c)))^2 + (1 : ℝ) * (((a * c * d) + ((-1) * a * b * d)))^2 + (1 : ℝ) * (((a * c * d) + ((-1) * a * b * c)))^2 + (1 : ℝ) * (((a * b * d) + ((-1) * a * b * c)))^2 := by positivity
      _ = (-(a * c * d + a * b * d + a * b * c + b * c * d) ^ 2 + 4 * a ^ 2 * c ^ 2 * d ^ 2 + 4 * a ^ 2 * b ^ 2 * d ^ 2 + 4 * a ^ 2 * b ^ 2 * c ^ 2 + 4 * b ^ 2 * c ^ 2 * d ^ 2) - (0) := by ring
  exact sub_nonneg.mp h
