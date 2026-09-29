-- Prove2me | solution 1 for lean_workbook_plus_78595
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:20:48.350103+00:00
-- url     : https://prove2.me/submissions/130527c3-5c69-4ea0-a6ec-f5ff0747844d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ x y : ℝ, x^2 + x*y + y^2 ≥ 3/4 * (x + y)^2 := by
  intro x y
  intros
  have h : (0 : ℝ) ≤ (x^2 + x*y + y^2) - (3/4 * (x + y)^2) := by
    calc
      0 ≤ ((1 / 4) : ℝ) * ((y + ((-1) * x)))^2 := by positivity
      _ = (x^2 + x*y + y^2) - (3/4 * (x + y)^2) := by ring
  exact sub_nonneg.mp h
