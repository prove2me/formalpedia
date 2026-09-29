-- Prove2me | solution 1 for lean_workbook_plus_67214
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:52:34.886818+00:00
-- url     : https://prove2.me/submissions/3d0cbc01-0029-4b4a-922e-468d8648275c

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b x y : ℝ) (hx: a > 0 ∧ b > 0 ∧ x > 0 ∧ y > 0) : (x ^ 2 / a + y ^ 2 / b) ≥ (x + y) ^ 2 / (a + b) := by
  rcases hx with ⟨ha,hb,hx,hy⟩
  apply (div_le_iff₀ (add_pos ha hb)).2
  field_simp
  nlinarith [sq_nonneg (x*b-y*a)]
