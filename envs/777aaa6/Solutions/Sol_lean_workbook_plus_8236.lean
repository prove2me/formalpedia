-- Prove2me | solution 1 for lean_workbook_plus_8236
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:43:51.224802+00:00
-- url     : https://prove2.me/submissions/6f2bc1af-cd39-4886-b180-3335de2272f4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) : x ^ 8 + x ^ 2 + 1 ≥ x ^ 5 + x := by
  intros
  have h : (0 : ℝ) ≤ (x ^ 8 + x ^ 2 + 1) - (x ^ 5 + x) := by
    calc
      0 ≤ ((2 / 3) : ℝ) * ((1 + ((-1) * x)))^2 + ((1 / 3) : ℝ) * ((1 + ((1 / 2) * x)))^2 + ((1 / 4) : ℝ) * ((x + ((-2) * (x ^ 4))))^2 := by positivity
      _ = (x ^ 8 + x ^ 2 + 1) - (x ^ 5 + x) := by ring
  exact sub_nonneg.mp h
