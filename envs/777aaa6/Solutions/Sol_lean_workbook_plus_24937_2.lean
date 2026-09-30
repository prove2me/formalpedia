-- Prove2me | solution 2 for lean_workbook_plus_24937
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:45:24.546989+00:00
-- url     : https://prove2.me/submissions/0c13166e-ad33-4940-84ed-4025b6edbb36

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) : 4 * x ^ 2 * y ^ 2 + x ^ 2 + y ^ 2 + 1 ≥ 6 * x * y := by
  intros
  have h : (0 : ℝ) ≤ (4 * x ^ 2 * y ^ 2 + x ^ 2 + y ^ 2 + 1) - (6 * x * y) := by
    calc
      0 ≤ (1 : ℝ) * ((1 + ((-2) * x * y)))^2 + (1 : ℝ) * ((y + ((-1) * x)))^2 := by positivity
      _ = (4 * x ^ 2 * y ^ 2 + x ^ 2 + y ^ 2 + 1) - (6 * x * y) := by ring
  exact sub_nonneg.mp h
