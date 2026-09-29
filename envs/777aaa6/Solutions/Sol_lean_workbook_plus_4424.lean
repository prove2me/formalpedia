-- Prove2me | solution 1 for lean_workbook_plus_4424
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:49:35.490988+00:00
-- url     : https://prove2.me/submissions/19412e4c-1f29-4ce6-b6dc-60e5c19fe562

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) (h₀ : 0 < x) (h₁ : 0 < y) : x^2 + (8/(x*y)) + y^2 >= 8 := by
  have hp : 0 < x*y := mul_pos h₀ h₁
  apply (mul_le_mul_iff_left₀ hp).mp
  rw [add_mul, add_mul, div_mul_cancel₀ 8 (ne_of_gt hp)]
  nlinarith [mul_nonneg hp.le (sq_nonneg (x-y)), sq_nonneg (x*y-2)]
