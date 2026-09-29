-- Prove2me | solution 1 for lean_workbook_plus_14238
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:15:23.684414+00:00
-- url     : https://prove2.me/submissions/1579a94e-63ca-4fd2-82ac-7a8987306ee3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) : (x^6 - x^5 + x^4 - x^3 + x^2 - x + 1) ≥ 1/2 := by
  intros
  have h : (0 : ℝ) ≤ ((x^6 - x^5 + x^4 - x^3 + x^2 - x + 1)) - (1/2) := by
    calc
      0 ≤ ((1 / 6) : ℝ) * ((1 + ((-1) * x)))^2 + ((1 / 6) : ℝ) * ((1 + ((-2) * x)))^2 + ((1 / 6) : ℝ) * ((1 + ((-1) * (x ^ 3))))^2 + ((1 / 6) : ℝ) * ((x + ((-2) * (x ^ 2))))^2 + ((1 / 6) : ℝ) * (((x ^ 2) + ((-1) * (x ^ 3))))^2 + ((1 / 6) : ℝ) * (((x ^ 2) + ((-2) * (x ^ 3))))^2 := by positivity
      _ = ((x^6 - x^5 + x^4 - x^3 + x^2 - x + 1)) - (1/2) := by ring
  exact sub_nonneg.mp h
