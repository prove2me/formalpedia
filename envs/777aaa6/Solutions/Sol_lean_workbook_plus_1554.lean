-- Prove2me | solution 1 for lean_workbook_plus_1554
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:32.19931+00:00
-- url     : https://prove2.me/submissions/d427b6a8-78e7-4b1d-9ce8-49c4de657a24

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : a * b * (a + Real.sqrt (1 + a^2)) ≤ 1)
  (h₂ : a^2 + b^2 = 1) :
  Real.sqrt (1 + a^2) ≤ (1 - a^2 * b) / (a * b) := by
  rcases h₀ with ⟨ha,hb⟩
  apply (le_div_iff₀ (mul_pos ha hb)).2
  nlinarith only [h₁]
