-- Prove2me | solution 1 for lean_workbook_plus_28143
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:19:17.1345+00:00
-- url     : https://prove2.me/submissions/3f92d6c0-7ef9-4252-8e19-564a5a8df022

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ x y z : ℝ, (x ^ 2 + y ^ 2 + z ^ 2) + 3 ≥ 2 * (x + y + z) := by
  intro x y z
  intros
  have h : (0 : ℝ) ≤ ((x ^ 2 + y ^ 2 + z ^ 2) + 3) - (2 * (x + y + z)) := by
    calc
      0 ≤ (1 : ℝ) * ((1 + ((-1) * z)))^2 + (1 : ℝ) * ((1 + ((-1) * y)))^2 + (1 : ℝ) * ((1 + ((-1) * x)))^2 := by positivity
      _ = ((x ^ 2 + y ^ 2 + z ^ 2) + 3) - (2 * (x + y + z)) := by ring
  exact sub_nonneg.mp h
