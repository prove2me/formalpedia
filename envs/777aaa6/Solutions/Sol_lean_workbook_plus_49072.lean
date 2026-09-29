-- Prove2me | solution 1 for lean_workbook_plus_49072
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:39:34.356315+00:00
-- url     : https://prove2.me/submissions/262b2421-da5d-48cb-ad80-9843c0e22911

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  intro a b c
  intros
  have h : (0 : ℝ) ≤ (3 * (a ^ 2 + b ^ 2 + c ^ 2)) - ((a + b + c) ^ 2) := by
    calc
      0 ≤ (1 : ℝ) * ((c + ((-1) * b)))^2 + (1 : ℝ) * ((c + ((-1) * a)))^2 + (1 : ℝ) * ((b + ((-1) * a)))^2 := by positivity
      _ = (3 * (a ^ 2 + b ^ 2 + c ^ 2)) - ((a + b + c) ^ 2) := by ring
  exact sub_nonneg.mp h
