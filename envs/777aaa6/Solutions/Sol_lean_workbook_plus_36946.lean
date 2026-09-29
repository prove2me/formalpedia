-- Prove2me | solution 1 for lean_workbook_plus_36946
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:26:23.896491+00:00
-- url     : https://prove2.me/submissions/094a3cfc-ac9f-4124-9098-13e82af6dec1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) : x^2 + y^2 + 2 ≥ (x + 1) * (y + 1) := by
  intros
  have h : (0 : ℝ) ≤ (x^2 + y^2 + 2) - ((x + 1) * (y + 1)) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * ((1 + ((-1) * y)))^2 + ((1 / 2) : ℝ) * ((1 + ((-1) * x)))^2 + ((1 / 2) : ℝ) * ((y + ((-1) * x)))^2 := by positivity
      _ = (x^2 + y^2 + 2) - ((x + 1) * (y + 1)) := by ring
  exact sub_nonneg.mp h
