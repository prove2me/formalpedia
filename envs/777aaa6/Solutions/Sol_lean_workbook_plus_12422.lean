-- Prove2me | solution 1 for lean_workbook_plus_12422
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:09:40.836748+00:00
-- url     : https://prove2.me/submissions/b0e93418-3a8e-4660-a948-7c4e54d8cb92

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) (hx : |x| ≤ 2) : ‖(2 * x ^ 2 + 3 * x + 2) / (x ^ 2 + 2)‖ ≤ 8 := by
  have hd : 0 < x^2+2 := by positivity
  rcases abs_le.mp hx with ⟨hl, hu⟩
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ hd).2
    nlinarith [sq_nonneg x]
  · apply (div_le_iff₀ hd).2
    nlinarith [sq_nonneg x]
