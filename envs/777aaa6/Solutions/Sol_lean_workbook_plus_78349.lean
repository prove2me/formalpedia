-- Prove2me | solution 1 for lean_workbook_plus_78349
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:19:51.326213+00:00
-- url     : https://prove2.me/submissions/9dc04ca1-1561-4484-9e48-afedf5103c25

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a b : ℝ, 2 * a ^ 2 * b ≤ a ^ 2 + a ^ 2 * b ^ 2 := by
  intro a b
  intros
  have h : (0 : ℝ) ≤ (a ^ 2 + a ^ 2 * b ^ 2) - (2 * a ^ 2 * b) := by
    calc
      0 ≤ (1 : ℝ) * ((a + ((-1) * a * b)))^2 := by positivity
      _ = (a ^ 2 + a ^ 2 * b ^ 2) - (2 * a ^ 2 * b) := by ring
  exact sub_nonneg.mp h
