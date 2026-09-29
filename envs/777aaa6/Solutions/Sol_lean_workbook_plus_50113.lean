-- Prove2me | solution 1 for lean_workbook_plus_50113
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:49:28.936777+00:00
-- url     : https://prove2.me/submissions/9b434544-7775-4689-812a-c4a3b77baf9b

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) (h : 1 ≤ x ∧ x ≤ 2) : x + 2 / x ≤ 3 := by
  have hx : 0 < x := by linarith [h.1]
  have he : x+2/x = (x^2+2)/x := by field_simp
  rw [he]
  apply (div_le_iff₀ hx).2
  nlinarith [mul_nonneg (sub_nonneg.mpr h.1) (sub_nonneg.mpr h.2)]
