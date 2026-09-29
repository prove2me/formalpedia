-- Prove2me | solution 1 for lean_workbook_plus_31955
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:28:47.595727+00:00
-- url     : https://prove2.me/submissions/6b6e0dc4-a104-4687-929f-7d4ae1f3c4fa

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) : (x^2 + y^2 + z^2)^3 ≥ 3 * (x^2 * y + y^2 * z + z^2 * x)^2 := by
  intros
  have h : (0 : ℝ) ≤ ((x^2 + y^2 + z^2)^3) - (3 * (x^2 * y + y^2 * z + z^2 * x)^2) := by
    calc
      0 ≤ (1 : ℝ) * (((z ^ 3) + ((-1) * x * (y ^ 2))))^2 + (2 : ℝ) * (((y * (z ^ 2)) + ((-1) * x * y * z)))^2 + (1 : ℝ) * ((((-1) * (x ^ 3)) + (y * (z ^ 2))))^2 + (1 : ℝ) * (((y ^ 3) + ((-1) * z * (x ^ 2))))^2 + (2 : ℝ) * ((((-1) * x * (y ^ 2)) + (x * y * z)))^2 + (2 : ℝ) * ((((-1) * z * (x ^ 2)) + (x * y * z)))^2 := by positivity
      _ = ((x^2 + y^2 + z^2)^3) - (3 * (x^2 * y + y^2 * z + z^2 * x)^2) := by ring
  exact sub_nonneg.mp h
