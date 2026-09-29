-- Prove2me | solution 1 for lean_workbook_plus_16437
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:20:27.467583+00:00
-- url     : https://prove2.me/submissions/b322a6e7-7fae-498d-a1b0-0d9a0a7f50ae

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a : ℝ, (a + 1) ^ 2 ≥ 4 * a := by
  intro a
  intros
  have h : (0 : ℝ) ≤ ((a + 1) ^ 2) - (4 * a) := by
    calc
      0 ≤ (1 : ℝ) * ((1 + ((-1) * a)))^2 := by positivity
      _ = ((a + 1) ^ 2) - (4 * a) := by ring
  exact sub_nonneg.mp h
