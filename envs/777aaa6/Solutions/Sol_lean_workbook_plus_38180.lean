-- Prove2me | solution 1 for lean_workbook_plus_38180
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:07:36.766808+00:00
-- url     : https://prove2.me/submissions/a7a98f31-9cae-449e-906e-e4b521904ecb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (b_i : ℝ) (h₁ : 0 < b_i) (h₂ : b_i < x) : (b_i / (b_i + 2)) ≤ (x / (x + 2)) ∧ (x / (x + 2)) < 1 := by
  have hx : 0 < x := lt_trans h₁ h₂
  have hb2 : 0 < b_i+2 := by linarith
  have hx2 : 0 < x+2 := by linarith
  constructor
  · apply (div_le_div_iff₀ hb2 hx2).2
    nlinarith
  · apply (div_lt_one hx2).2
    linarith
