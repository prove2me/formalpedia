-- Prove2me | solution 1 for lean_workbook_plus_5691
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:25:53.158964+00:00
-- url     : https://prove2.me/submissions/9a45cc4a-b5f6-4391-af0c-ec63bf97b0da

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (u v : ℝ) (hu : u > 0) (hv : v > 0) : (1 / (1 + u) ^ 2 + 1 / (1 + v) ^ 2) ≥ 1 / (1 + u * v) := by
  have hU : 0 < 1 + u := by linarith
  have hV : 0 < 1 + v := by linarith
  have hUV : 0 < 1 + u * v := by positivity
  have heq : (1 / (1 + u) ^ 2 + 1 / (1 + v) ^ 2) - 1 / (1 + u * v) = ((1 - u * v) ^ 2 + u * v * (u - v) ^ 2) / ((1 + u) ^ 2 * (1 + v) ^ 2 * (1 + u * v)) := by
    field_simp [ne_of_gt hU, ne_of_gt hV, ne_of_gt hUV]
    <;> ring
  apply sub_nonneg.mp
  rw [heq]
  exact div_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg (le_of_lt (mul_pos hu hv)) (sq_nonneg _))) (by positivity)
