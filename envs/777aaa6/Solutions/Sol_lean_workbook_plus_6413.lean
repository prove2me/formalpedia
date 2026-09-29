-- Prove2me | solution 1 for lean_workbook_plus_6413
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:24:05.9837+00:00
-- url     : https://prove2.me/submissions/be993eee-3dab-480d-99e8-12940c99a023

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a b c : ℝ, (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  intro a b c
  intros
  have h : (0 : ℝ) ≤ (3 * (a ^ 2 + b ^ 2 + c ^ 2)) - ((a + b + c) ^ 2) := by
    calc
      0 ≤ (1 : ℝ) * ((c + ((-1) * b)))^2 + (1 : ℝ) * ((c + ((-1) * a)))^2 + (1 : ℝ) * ((b + ((-1) * a)))^2 := by positivity
      _ = (3 * (a ^ 2 + b ^ 2 + c ^ 2)) - ((a + b + c) ^ 2) := by ring
  exact sub_nonneg.mp h
