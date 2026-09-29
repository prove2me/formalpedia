-- Prove2me | solution 1 for lean_workbook_plus_2743
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:19:37.139761+00:00
-- url     : https://prove2.me/submissions/6122fb7d-0db8-4c2a-a63d-be22fd8e7d76

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) : 3 * (a ^ 4 * (b ^ 2 + c ^ 2) + b ^ 4 * (c ^ 2 + a ^ 2) + c ^ 4 * (a ^ 2 + b ^ 2)) + 6 * a ^ 2 * b ^ 2 * c ^ 2 ≥ 4 * a * b * c * (a ^ 2 * (b + c) + b ^ 2 * (c + a) + c ^ 2 * (a + b)) := by
  intros
  have h : (0 : ℝ) ≤ (3 * (a ^ 4 * (b ^ 2 + c ^ 2) + b ^ 4 * (c ^ 2 + a ^ 2) + c ^ 4 * (a ^ 2 + b ^ 2)) + 6 * a ^ 2 * b ^ 2 * c ^ 2) - (4 * a * b * c * (a ^ 2 * (b + c) + b ^ 2 * (c + a) + c ^ 2 * (a + b))) := by
    calc
      0 ≤ (1 : ℝ) * (((b * (c ^ 2)) + ((-1) * a * b * c)))^2 + (2 : ℝ) * (((b * (c ^ 2)) + ((-1) * a * (b ^ 2))))^2 + (1 : ℝ) * (((c * (b ^ 2)) + ((-1) * a * (c ^ 2))))^2 + (2 : ℝ) * (((c * (b ^ 2)) + ((-1) * b * (a ^ 2))))^2 + (2 : ℝ) * (((a * (c ^ 2)) + ((-1) * a * b * c)))^2 + (2 : ℝ) * ((((-1) * c * (a ^ 2)) + (a * b * c)))^2 + (1 : ℝ) * ((((-1) * b * (a ^ 2)) + (a * b * c)))^2 + (1 : ℝ) * (((a * (b ^ 2)) + ((-1) * c * (a ^ 2))))^2 := by positivity
      _ = (3 * (a ^ 4 * (b ^ 2 + c ^ 2) + b ^ 4 * (c ^ 2 + a ^ 2) + c ^ 4 * (a ^ 2 + b ^ 2)) + 6 * a ^ 2 * b ^ 2 * c ^ 2) - (4 * a * b * c * (a ^ 2 * (b + c) + b ^ 2 * (c + a) + c ^ 2 * (a + b))) := by ring
  exact sub_nonneg.mp h
