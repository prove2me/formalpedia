-- Prove2me | solution 1 for lean_workbook_plus_9073
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:25:50.446762+00:00
-- url     : https://prove2.me/submissions/5d89ab62-d78f-406d-a801-e506b5ee6c4a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (1 / (1 + a) ^ 2 + 1 / (1 + b) ^ 2) ≥ 1 / (1 + a * b) := by
  have hA : 0 < 1 + a := by linarith
  have hB : 0 < 1 + b := by linarith
  have hAB : 0 < 1 + a * b := by positivity
  have heq : (1 / (1 + a) ^ 2 + 1 / (1 + b) ^ 2) - 1 / (1 + a * b) = ((1 - a * b) ^ 2 + a * b * (a - b) ^ 2) / ((1 + a) ^ 2 * (1 + b) ^ 2 * (1 + a * b)) := by
    field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hAB]
    <;> ring
  apply sub_nonneg.mp
  rw [heq]
  exact div_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg ha hb) (sq_nonneg _))) (by positivity)
