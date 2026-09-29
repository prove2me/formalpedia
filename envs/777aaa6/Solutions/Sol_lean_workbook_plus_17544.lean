-- Prove2me | solution 1 for lean_workbook_plus_17544
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:36:45.011775+00:00
-- url     : https://prove2.me/submissions/5eea4021-6dc8-491c-b7fa-d879d6a6878b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) : (x ^ 2 + y ^ 2) * (y ^ 2 + z ^ 2) * (z ^ 2 + x ^ 2) ≥ (x ^ 2 + 2 * y ^ 2 - z ^ 2) * (y ^ 2 + 2 * z ^ 2 - x ^ 2) * (z ^ 2 + 2 * x ^ 2 - y ^ 2) := by
  intros
  have h : (0 : ℝ) ≤ ((x ^ 2 + y ^ 2) * (y ^ 2 + z ^ 2) * (z ^ 2 + x ^ 2)) - ((x ^ 2 + 2 * y ^ 2 - z ^ 2) * (y ^ 2 + 2 * z ^ 2 - x ^ 2) * (z ^ 2 + 2 * x ^ 2 - y ^ 2)) := by
    calc
      0 ≤ (2 : ℝ) * (((z ^ 3) + ((-1) * z * (y ^ 2))))^2 + (2 : ℝ) * (((y ^ 3) + ((-1) * y * (x ^ 2))))^2 + (2 : ℝ) * ((((-1) * (x ^ 3)) + (x * (z ^ 2))))^2 := by positivity
      _ = ((x ^ 2 + y ^ 2) * (y ^ 2 + z ^ 2) * (z ^ 2 + x ^ 2)) - ((x ^ 2 + 2 * y ^ 2 - z ^ 2) * (y ^ 2 + 2 * z ^ 2 - x ^ 2) * (z ^ 2 + 2 * x ^ 2 - y ^ 2)) := by ring
  exact sub_nonneg.mp h
