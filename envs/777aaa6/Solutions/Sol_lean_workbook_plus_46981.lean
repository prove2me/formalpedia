-- Prove2me | solution 1 for lean_workbook_plus_46981
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:49.522314+00:00
-- url     : https://prove2.me/submissions/7fe5c6e6-1b79-4953-8ede-775b1ce0476e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c p : ℝ)
  (h₀ : 0 < p ∧ p ≠ 1)
  (h₁ : a ≠ 0)
  (h₂ : (p - 1) * (p + 1) = 1)
  (h₃ : b = -a * (2 * p^2 - 1) / (p * (p - 1)))
  (h₄ : c = a * (p + 1) / (p - 1)) :
  b^2 - 4 * a * c = a^2 / (p^2 * (p - 1)^2) := by
  clear h₂ h₁
  rw [h₃, h₄]
  have hp : p ≠ 0 := ne_of_gt h₀.1
  have hp1 : p - 1 ≠ 0 := sub_ne_zero.mpr h₀.2
  field_simp [hp, hp1] <;> ring
