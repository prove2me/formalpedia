-- Prove2me | solution 1 for lean_workbook_plus_18267
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:05:11.24117+00:00
-- url     : https://prove2.me/submissions/946f4e60-4a9b-4448-a5a8-3d8611d271ae

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b : ℝ)
  (h₀ : a ≠ 0 ∧ b ≠ 0)
  (h₁ : a ≠ b) :
  1 / (1 / a^3 - 1 / b^3) = a^3 * b^3 / (b^3 - a^3) := by
  clear h₁
  rw [div_sub_div 1 1 (pow_ne_zero 3 h₀.1) (pow_ne_zero 3 h₀.2)]
  simp only [one_mul,mul_one,one_div_div]
