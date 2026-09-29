-- Prove2me | solution 1 for lean_workbook_plus_8392
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:18:21.531313+00:00
-- url     : https://prove2.me/submissions/e169dce5-73fd-4ba8-84f0-13594585a0ef

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) : (x ^ 3 * y + y ^ 3 * z + z ^ 3 * x) * (x * y + y * z + z * x) ≥ (x + y + z) * x * y * z * (x ^ 2 + y ^ 2 + z ^ 2) := by
  intros
  have h : (0 : ℝ) ≤ ((x ^ 3 * y + y ^ 3 * z + z ^ 3 * x) * (x * y + y * z + z * x)) - ((x + y + z) * x * y * z * (x ^ 2 + y ^ 2 + z ^ 2)) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * (((z * (y ^ 2)) + ((-1) * x * (z ^ 2))))^2 + ((1 / 2) : ℝ) * (((z * (y ^ 2)) + ((-1) * y * (x ^ 2))))^2 + ((1 / 2) : ℝ) * (((x * (z ^ 2)) + ((-1) * y * (x ^ 2))))^2 := by positivity
      _ = ((x ^ 3 * y + y ^ 3 * z + z ^ 3 * x) * (x * y + y * z + z * x)) - ((x + y + z) * x * y * z * (x ^ 2 + y ^ 2 + z ^ 2)) := by ring
  exact sub_nonneg.mp h
