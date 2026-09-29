-- Prove2me | solution 1 for lean_workbook_plus_69506
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:18:02.496908+00:00
-- url     : https://prove2.me/submissions/b5e0410c-37e2-4cb5-a310-4272a5b633c2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) : (x^6 + 1) / 2 ≥ x^3 := by
  intros
  have h : (0 : ℝ) ≤ ((x^6 + 1) / 2) - (x^3) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * ((1 + ((-1) * (x ^ 3))))^2 := by positivity
      _ = ((x^6 + 1) / 2) - (x^3) := by ring
  exact sub_nonneg.mp h
