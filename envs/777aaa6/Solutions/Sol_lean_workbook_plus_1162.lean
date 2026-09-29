-- Prove2me | solution 1 for lean_workbook_plus_1162
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:44:46.032974+00:00
-- url     : https://prove2.me/submissions/8ed9678e-8653-451d-8ae8-bf1605ea665f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ x y z : ℝ, 28 * (x ^ 4 + y ^ 4 + z ^ 4) ≥ (x + y + z) ^ 4 + (y + z - x) ^ 4 + (z + x - y) ^ 4 + (x + y - z) ^ 4 := by
  intro x y z
  intros
  have h : (0 : ℝ) ≤ (28 * (x ^ 4 + y ^ 4 + z ^ 4)) - ((x + y + z) ^ 4 + (y + z - x) ^ 4 + (z + x - y) ^ 4 + (x + y - z) ^ 4) := by
    calc
      0 ≤ (12 : ℝ) * (((z ^ 2) + ((-1) * (y ^ 2))))^2 + (12 : ℝ) * (((z ^ 2) + ((-1) * (x ^ 2))))^2 + (12 : ℝ) * (((y ^ 2) + ((-1) * (x ^ 2))))^2 := by positivity
      _ = (28 * (x ^ 4 + y ^ 4 + z ^ 4)) - ((x + y + z) ^ 4 + (y + z - x) ^ 4 + (z + x - y) ^ 4 + (x + y - z) ^ 4) := by ring
  exact sub_nonneg.mp h
