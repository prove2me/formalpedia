-- Prove2me | solution 1 for lean_workbook_plus_18633
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:19:44.704713+00:00
-- url     : https://prove2.me/submissions/43b53b1d-8777-4315-b949-2ba2862da291

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ x y z : ℝ, x * y + y * z + z * x ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
  intro x y z
  intros
  have h : (0 : ℝ) ≤ (x ^ 2 + y ^ 2 + z ^ 2) - (x * y + y * z + z * x) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * ((z + ((-1) * y)))^2 + ((1 / 2) : ℝ) * ((z + ((-1) * x)))^2 + ((1 / 2) : ℝ) * ((y + ((-1) * x)))^2 := by positivity
      _ = (x ^ 2 + y ^ 2 + z ^ 2) - (x * y + y * z + z * x) := by ring
  exact sub_nonneg.mp h
