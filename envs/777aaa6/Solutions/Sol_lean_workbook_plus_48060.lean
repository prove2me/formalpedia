-- Prove2me | solution 1 for lean_workbook_plus_48060
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:40:54.061599+00:00
-- url     : https://prove2.me/submissions/44501019-0f1c-455e-a087-78decfe737f5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a : ℝ) : (1 + 3 * a ^ 2) ^ 2 ≥ 16 * a ^ 3 := by
  intros
  have h : (0 : ℝ) ≤ ((1 + 3 * a ^ 2) ^ 2) - (16 * a ^ 3) := by
    calc
      0 ≤ (1 : ℝ) * ((1 + ((-1) * (a ^ 2))))^2 + (8 : ℝ) * ((a + ((-1) * (a ^ 2))))^2 := by positivity
      _ = ((1 + 3 * a ^ 2) ^ 2) - (16 * a ^ 3) := by ring
  exact sub_nonneg.mp h
