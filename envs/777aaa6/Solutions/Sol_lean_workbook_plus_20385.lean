-- Prove2me | solution 1 for lean_workbook_plus_20385
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:17:30.086923+00:00
-- url     : https://prove2.me/submissions/6cecb69a-9d6d-49f6-a7a6-4e24d1761200

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ x : ℝ, 10 * x ^ 6 - 24 * x ^ 5 + 15 * x ^ 4 + 40 * x ^ 2 ≥ 0 := by
  intro x
  intros
  have h : (0 : ℝ) ≤ (10 * x ^ 6 - 24 * x ^ 5 + 15 * x ^ 4 + 40 * x ^ 2) - (0) := by
    calc
      0 ≤ (38 : ℝ) * (x)^2 + (2 : ℝ) * ((x + ((-1 / 2) * (x ^ 3))))^2 + (7 : ℝ) * (((x ^ 2) + ((-1) * (x ^ 3))))^2 + (10 : ℝ) * (((x ^ 2) + ((-1 / 2) * (x ^ 3))))^2 := by positivity
      _ = (10 * x ^ 6 - 24 * x ^ 5 + 15 * x ^ 4 + 40 * x ^ 2) - (0) := by ring
  exact sub_nonneg.mp h
