-- Prove2me | solution 1 for lean_workbook_plus_23944
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:17:44.836715+00:00
-- url     : https://prove2.me/submissions/22610b15-d86c-4bfd-93d1-acd0f7f1f8bf

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) : (x^4 + y^4 + z^4) * (x^2 * y^2 + y^2 * z^2 + z^2 * x^2) ≥ (x * y^3 + y * z^3 + x^3 * z)^2 := by
  intros
  have h : (0 : ℝ) ≤ ((x^4 + y^4 + z^4) * (x^2 * y^2 + y^2 * z^2 + z^2 * x^2)) - ((x * y^3 + y * z^3 + x^3 * z)^2) := by
    calc
      0 ≤ (1 : ℝ) * (((z * (y ^ 3)) + ((-1) * x * y * (z ^ 2))))^2 + (1 : ℝ) * (((x * (z ^ 3)) + ((-1) * y * z * (x ^ 2))))^2 + (1 : ℝ) * ((((-1) * y * (x ^ 3)) + (x * z * (y ^ 2))))^2 := by positivity
      _ = ((x^4 + y^4 + z^4) * (x^2 * y^2 + y^2 * z^2 + z^2 * x^2)) - ((x * y^3 + y * z^3 + x^3 * z)^2) := by ring
  exact sub_nonneg.mp h
