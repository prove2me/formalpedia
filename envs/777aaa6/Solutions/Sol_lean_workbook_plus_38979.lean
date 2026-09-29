-- Prove2me | solution 1 for lean_workbook_plus_38979
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:15:32.659961+00:00
-- url     : https://prove2.me/submissions/ce40eb42-2a21-40fd-ab06-29669f566bfa

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) : 9 * (x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 4 + 2 * y ^ 2 * x ^ 2 + 2 * x ^ 2 * z ^ 2 + y ^ 4 + 2 * y ^ 2 * z ^ 2 + z ^ 4 - 3 * y * z ^ 2 * x - 3 * y * z * x ^ 2 - 3 * y ^ 2 * z * x) ≥ 0 := by
  intros
  have h : (0 : ℝ) ≤ (9 * (x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 4 + 2 * y ^ 2 * x ^ 2 + 2 * x ^ 2 * z ^ 2 + y ^ 4 + 2 * y ^ 2 * z ^ 2 + z ^ 4 - 3 * y * z ^ 2 * x - 3 * y * z * x ^ 2 - 3 * y ^ 2 * z * x)) - (0) := by
    calc
      0 ≤ ((9 / 2) : ℝ) * (((z ^ 3) + ((-1) * x * y * z)))^2 + ((9 / 2) : ℝ) * (((z ^ 3) + ((-1) * y * (x ^ 2))))^2 + (9 : ℝ) * (((y * (z ^ 2)) + ((-1) * x * (z ^ 2))))^2 + (9 : ℝ) * (((y * (z ^ 2)) + ((-1) * x * y * z)))^2 + (9 : ℝ) * (((y * (z ^ 2)) + ((-1) * z * (x ^ 2))))^2 + ((9 / 2) : ℝ) * (((z * (y ^ 2)) + ((-1) * x * (z ^ 2))))^2 + ((27 / 2) : ℝ) * (((z * (y ^ 2)) + ((-1) * x * y * z)))^2 + ((9 / 2) : ℝ) * (((z * (y ^ 2)) + ((-1) * x * (y ^ 2))))^2 + ((9 / 2) : ℝ) * ((((-1) * (x ^ 3)) + (z * (y ^ 2))))^2 + (9 : ℝ) * (((y ^ 3) + ((-1) * x * y * z)))^2 + ((27 / 2) : ℝ) * (((x * (z ^ 2)) + ((-1) * y * (x ^ 2))))^2 + ((27 / 2) : ℝ) * ((((-1) * x * (y ^ 2)) + (x * y * z)))^2 + ((9 / 2) : ℝ) * ((((-1) * (x ^ 3)) + (x * y * z)))^2 + (9 : ℝ) * (((x * (y ^ 2)) + ((-1) * z * (x ^ 2))))^2 + (9 : ℝ) * (((z * (x ^ 2)) + ((-1) * y * (x ^ 2))))^2 := by positivity
      _ = (9 * (x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 4 + 2 * y ^ 2 * x ^ 2 + 2 * x ^ 2 * z ^ 2 + y ^ 4 + 2 * y ^ 2 * z ^ 2 + z ^ 4 - 3 * y * z ^ 2 * x - 3 * y * z * x ^ 2 - 3 * y ^ 2 * z * x)) - (0) := by ring
  exact sub_nonneg.mp h
