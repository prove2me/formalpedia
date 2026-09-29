-- Prove2me | solution 1 for lean_workbook_plus_65607
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:17:34.480188+00:00
-- url     : https://prove2.me/submissions/d6215e13-8ad7-40c4-ba1e-3249ee5d28ed

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) : (x^2 + y^2 + z^2) * (y^2 * z^2 + z^2 * x^2 + x^2 * y^2) ≥ (x^2 * y + y^2 * z + z^2 * x)^2 := by
  intros
  have h : (0 : ℝ) ≤ ((x^2 + y^2 + z^2) * (y^2 * z^2 + z^2 * x^2 + x^2 * y^2)) - ((x^2 * y + y^2 * z + z^2 * x)^2) := by
    calc
      0 ≤ (1 : ℝ) * (((y * (z ^ 2)) + ((-1) * x * y * z)))^2 + (1 : ℝ) * ((((-1) * x * (y ^ 2)) + (x * y * z)))^2 + (1 : ℝ) * ((((-1) * z * (x ^ 2)) + (x * y * z)))^2 := by positivity
      _ = ((x^2 + y^2 + z^2) * (y^2 * z^2 + z^2 * x^2 + x^2 * y^2)) - ((x^2 * y + y^2 * z + z^2 * x)^2) := by ring
  exact sub_nonneg.mp h
