-- Prove2me | solution 1 for lean_workbook_plus_18943
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:20:57.461107+00:00
-- url     : https://prove2.me/submissions/3a31b170-ebed-48b6-b443-ba0adf2600f2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) : x - x^2 ≤ 1/4 := by
  intros
  have h : (0 : ℝ) ≤ (1/4) - (x - x^2) := by
    calc
      0 ≤ ((1 / 4) : ℝ) * ((1 + ((-2) * x)))^2 := by positivity
      _ = (1/4) - (x - x^2) := by ring
  exact sub_nonneg.mp h
