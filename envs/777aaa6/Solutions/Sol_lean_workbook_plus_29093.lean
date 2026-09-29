-- Prove2me | solution 1 for lean_workbook_plus_29093
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:41:52.835747+00:00
-- url     : https://prove2.me/submissions/37b095d4-58b2-4b8e-961b-e2a32a0f0f03

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ x y : ℝ, x ^ 2 - x * y + y ^ 2 ≤ (3 / 2) * (x ^ 2 + y ^ 2) := by
  intro x y
  intros
  have h : (0 : ℝ) ≤ ((3 / 2) * (x ^ 2 + y ^ 2)) - (x ^ 2 - x * y + y ^ 2) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * ((x + y))^2 := by positivity
      _ = ((3 / 2) * (x ^ 2 + y ^ 2)) - (x ^ 2 - x * y + y ^ 2) := by ring
  exact sub_nonneg.mp h
