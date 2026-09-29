-- Prove2me | solution 1 for lean_workbook_plus_41536
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:11:12.388535+00:00
-- url     : https://prove2.me/submissions/a5b9357a-3dce-4cd5-af29-0f6301cdad68

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x y : ℝ) (hx : x ≥ 1) (hy : y ≥ 1) (hxy : x ≥ y) :
  x + 1/x - (y + 1/y) ≥ 0 := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hprod : 1 ≤ x * y := by
    nlinarith [mul_nonneg (show 0 ≤ x - 1 by linarith) (show 0 ≤ y - 1 by linarith)]
  have heq : x + 1 / x - (y + 1 / y) = (x - y) * (x * y - 1) / (x * y) := by
    field_simp [ne_of_gt hx0, ne_of_gt hy0]
    <;> ring
  rw [heq]
  exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (le_of_lt (mul_pos hx0 hy0))
