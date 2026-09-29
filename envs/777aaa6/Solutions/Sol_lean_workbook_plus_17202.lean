-- Prove2me | solution 1 for lean_workbook_plus_17202
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:21:04.033803+00:00
-- url     : https://prove2.me/submissions/b381e226-64a7-4d1a-8033-4299f5a612cc

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x < 1) :
  x * (1 - x) ≤ 1 / 4 := by
  intros
  have h : (0 : ℝ) ≤ (1 / 4) - (x * (1 - x)) := by
    calc
      0 ≤ ((1 / 4) : ℝ) * ((1 + ((-2) * x)))^2 := by positivity
      _ = (1 / 4) - (x * (1 - x)) := by ring
  exact sub_nonneg.mp h
