-- Prove2me | solution 1 for lean_workbook_plus_70868
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:17:52.668261+00:00
-- url     : https://prove2.me/submissions/387c1b51-a031-4296-bbb3-89518dc24ac7

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b ≥ 3) : (a + 1 / b + 1) * (b + 1 / a + 1) ≥ 10 := by
  have hp : 0 < a*b := mul_pos ha hb
  have he : ((a+1/b+1)*(b+1/a+1))*(a*b) = (a*b)^2+(a+b+3)*(a*b)+a+b+1 := by
    field_simp [ne_of_gt ha, ne_of_gt hb] <;> ring
  apply (mul_le_mul_iff_left₀ hp).mp
  rw [he]
  have hs : 0 ≤ a+b-3 := by linarith
  have hq : 0 ≤ a*b+1 := by positivity
  nlinarith [sq_nonneg (a*b-2), mul_nonneg hs hq]
