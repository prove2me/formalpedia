-- Prove2me | solution 1 for lean_workbook_plus_28886
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:38:05.38422+00:00
-- url     : https://prove2.me/submissions/209f6ca7-5de3-45a1-a682-274378e6c44e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) : 4 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2) * (4 / 3) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
  intros
  have h : (0 : ℝ) ≤ ((a ^ 2 + b ^ 2 + c ^ 2) * (4 / 3) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2) - (4 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) ^ 2) := by
    calc
      0 ≤ ((4 / 3) : ℝ) * (((c ^ 3) + ((-1) * a * (b ^ 2))))^2 + ((8 / 3) : ℝ) * (((b * (c ^ 2)) + ((-1) * a * b * c)))^2 + ((4 / 3) : ℝ) * ((((-1) * (a ^ 3)) + (b * (c ^ 2))))^2 + ((4 / 3) : ℝ) * (((b ^ 3) + ((-1) * c * (a ^ 2))))^2 + ((8 / 3) : ℝ) * ((((-1) * a * (b ^ 2)) + (a * b * c)))^2 + ((8 / 3) : ℝ) * ((((-1) * c * (a ^ 2)) + (a * b * c)))^2 := by positivity
      _ = ((a ^ 2 + b ^ 2 + c ^ 2) * (4 / 3) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2) - (4 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) ^ 2) := by ring
  exact sub_nonneg.mp h
