-- Prove2me | solution 1 for lean_workbook_plus_76601
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:39:42.507257+00:00
-- url     : https://prove2.me/submissions/a5c6a900-8966-469d-b9e9-6b5277de1f85

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a b c : ℝ, (a + 3 * b) ^ 2 + (3 * b + 2 * c) ^ 2 ≥ (a + 6 * b + 2 * c) ^ 2 / 2 := by
  intro a b c
  intros
  have h : (0 : ℝ) ≤ ((a + 3 * b) ^ 2 + (3 * b + 2 * c) ^ 2) - ((a + 6 * b + 2 * c) ^ 2 / 2) := by
    calc
      0 ≤ (2 : ℝ) * ((c + ((-1 / 2) * a)))^2 := by positivity
      _ = ((a + 3 * b) ^ 2 + (3 * b + 2 * c) ^ 2) - ((a + 6 * b + 2 * c) ^ 2 / 2) := by ring
  exact sub_nonneg.mp h
