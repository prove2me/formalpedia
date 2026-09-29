-- Prove2me | solution 1 for lean_workbook_plus_8941
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:07:41.139778+00:00
-- url     : https://prove2.me/submissions/46de6658-2273-4bf9-a223-21e2b79f0271

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : 1 < a) (hb : 1 < b) : a^2 / (b - 1) + b^2 / (a - 1) ≥ 8 := by
  have hda : 0 < a-1 := sub_pos.mpr ha
  have hdb : 0 < b-1 := sub_pos.mpr hb
  have hd : 0 < (a-1)*(b-1) := mul_pos hda hdb
  have he : (a^2/(b-1)+b^2/(a-1))*((a-1)*(b-1)) = a^2*(a-1)+b^2*(b-1) := by
    field_simp [ne_of_gt hda, ne_of_gt hdb] <;> ring
  apply (mul_le_mul_iff_left₀ hd).mp
  rw [he]
  have hs : 0 ≤ a+b-2 := by linarith
  have ht : 0 ≤ a+b+2 := by linarith
  nlinarith [mul_nonneg hs (sq_nonneg (a+b-4)), mul_nonneg ht (sq_nonneg (a-b))]
