-- Prove2me | solution 1 for lean_workbook_plus_40069
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:09:50.162752+00:00
-- url     : https://prove2.me/submissions/1f47ef91-9fd4-46d1-a8a9-62798668c265

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y : ℝ) (h₁ : y = (x^2 + x + 1) / (x^2 + 1)) : 1 / 2 ≤ y ∧ y ≤ 3 / 2 := by
  have hd : 0 < x^2+1 := by positivity
  rw [h₁]
  constructor
  · apply (le_div_iff₀ hd).2
    nlinarith [sq_nonneg (x+1)]
  · apply (div_le_iff₀ hd).2
    nlinarith [sq_nonneg (x-1)]
