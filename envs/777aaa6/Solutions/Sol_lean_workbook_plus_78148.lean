-- Prove2me | solution 1 for lean_workbook_plus_78148
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:19:27.950161+00:00
-- url     : https://prove2.me/submissions/c0065084-1396-4f35-8810-4685efbc3494

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ x y : ℝ, x^2 + y^2 ≥ 2 * x * y := by
  intro x y
  intros
  have h : (0 : ℝ) ≤ (x^2 + y^2) - (2 * x * y) := by
    calc
      0 ≤ (1 : ℝ) * ((y + ((-1) * x)))^2 := by positivity
      _ = (x^2 + y^2) - (2 * x * y) := by ring
  exact sub_nonneg.mp h
