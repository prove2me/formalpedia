-- Prove2me | solution 1 for lean_workbook_plus_2944
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:14:57.831553+00:00
-- url     : https://prove2.me/submissions/c716682a-6d95-41fe-a304-b519632b6178

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) : x^4 + y^4 + (x^2 + 1) * (y^2 + 1) ≥ x^3 * (1 + y) + y^3 * (1 + x) + x + y := by
  intros
  have h : (0 : ℝ) ≤ (x^4 + y^4 + (x^2 + 1) * (y^2 + 1)) - (x^3 * (1 + y) + y^3 * (1 + x) + x + y) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * ((1 + ((-1) * y)))^2 + ((1 / 2) : ℝ) * ((1 + ((-1) * x)))^2 + ((1 / 2) : ℝ) * ((y + ((-1) * (y ^ 2))))^2 + ((1 / 2) : ℝ) * (((y ^ 2) + ((-1) * x * y)))^2 + ((1 / 2) : ℝ) * ((x + ((-1) * (x ^ 2))))^2 + ((1 / 2) : ℝ) * ((((-1) * (x ^ 2)) + (x * y)))^2 := by positivity
      _ = (x^4 + y^4 + (x^2 + 1) * (y^2 + 1)) - (x^3 * (1 + y) + y^3 * (1 + x) + x + y) := by ring
  exact sub_nonneg.mp h
