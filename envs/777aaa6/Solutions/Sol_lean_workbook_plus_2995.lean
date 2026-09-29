-- Prove2me | solution 1 for lean_workbook_plus_2995
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:18:24.266932+00:00
-- url     : https://prove2.me/submissions/1707e542-7115-413e-b404-465337370c24

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) : 2 * (a ^ 2 - a + 1) * (b ^ 2 - b + 1) - (a + b - 1) ^ 2 - 1 ≥ 0 := by
  intros
  have h : (0 : ℝ) ≤ (2 * (a ^ 2 - a + 1) * (b ^ 2 - b + 1) - (a + b - 1) ^ 2 - 1) - (0) := by
    calc
      0 ≤ (1 : ℝ) * ((b + ((-1) * a * b)))^2 + (1 : ℝ) * ((a + ((-1) * a * b)))^2 := by positivity
      _ = (2 * (a ^ 2 - a + 1) * (b ^ 2 - b + 1) - (a + b - 1) ^ 2 - 1) - (0) := by ring
  exact sub_nonneg.mp h
