-- Prove2me | solution 1 for lean_workbook_plus_47189
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:45:17.461699+00:00
-- url     : https://prove2.me/submissions/b1bf1e0e-d69f-4f79-ab2e-d0de14ec0bef

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 → 3 * (x ^ 2 + x * y + y ^ 2) * (y ^ 2 + y * z + z ^ 2) * (z ^ 2 + z * x + x ^ 2) ≥ (x + y + z) ^ 2 * (x * y + x * z + y * z) ^ 2 := by
  intro x y z
  intros
  have hpos_x : (0 : ℝ) ≤ x := by first | positivity | linarith
  have hpos_y : (0 : ℝ) ≤ y := by first | positivity | linarith
  have hpos_z : (0 : ℝ) ≤ z := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (3 * (x ^ 2 + x * y + y ^ 2) * (y ^ 2 + y * z + z ^ 2) * (z ^ 2 + z * x + x ^ 2)) - ((x + y + z) ^ 2 * (x * y + x * z + y * z) ^ 2) := by
    calc
      0 ≤ (1 : ℝ) * (1) * (((y * (x ^ 2)) + ((-1) * x * (z ^ 2))))^2 + (1 : ℝ) * (1) * (((y * (x ^ 2)) + ((-1) * z * (y ^ 2))))^2 + (1 : ℝ) * (1) * (((z * (x ^ 2)) + ((-1) * x * (y ^ 2))))^2 + (1 : ℝ) * (1) * (((z * (x ^ 2)) + ((-1) * y * (z ^ 2))))^2 + (1 : ℝ) * (1) * (((x * (y ^ 2)) + ((-1) * y * (z ^ 2))))^2 + (1 : ℝ) * (1) * (((x * (z ^ 2)) + ((-1) * z * (y ^ 2))))^2 + (1 : ℝ) * ((y * z)) * (((x ^ 2) + ((-1) * y * z)))^2 + (1 : ℝ) * ((x * z)) * ((((-1) * (y ^ 2)) + (x * z)))^2 + (1 : ℝ) * ((x * y)) * ((((-1) * (z ^ 2)) + (x * y)))^2 := by positivity
      _ = (3 * (x ^ 2 + x * y + y ^ 2) * (y ^ 2 + y * z + z ^ 2) * (z ^ 2 + z * x + x ^ 2)) - ((x + y + z) ^ 2 * (x * y + x * z + y * z) ^ 2) := by ring
  exact sub_nonneg.mp h
