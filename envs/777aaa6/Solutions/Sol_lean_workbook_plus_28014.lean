-- Prove2me | solution 1 for lean_workbook_plus_28014
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:46:23.011024+00:00
-- url     : https://prove2.me/submissions/9598fe03-5ecb-4f80-bab5-e6d56010d2b3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (z : ℝ) (hz: 0 ≤ z ∧ z ≤ 1) : z ≥ z^2 ∧ (z = z^2 ↔ z = 0 ∨ z = 1) := by
  constructor
  · nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
  · constructor
    · intro he
      have hf : z*(z-1)=0 := by nlinarith
      rcases mul_eq_zero.mp hf with h0|h1
      · exact Or.inl h0
      · exact Or.inr (by linarith)
    · rintro (rfl|rfl) <;> norm_num
