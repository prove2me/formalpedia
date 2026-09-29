-- Prove2me | solution 1 for lean_workbook_plus_67020
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:55:42.814054+00:00
-- url     : https://prove2.me/submissions/aeb2871a-922e-4be9-bbe8-0059fc1a2475

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∃ x : ℕ → ℝ, ∀ n : ℕ, n ≠ 4 ∧ n > 0 → x n = 1 / (4 - n) := by
  intros
  simp only [← funext_iff] at *
  simp_all
