-- Prove2me | solution 1 for lean_workbook_plus_54915
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:07:37.812387+00:00
-- url     : https://prove2.me/submissions/079e7f6d-54c5-4e38-bc7b-bd885510bd17

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b) :
  1 / a^2 + 1 / b^2 ≥ 8 / (a + b)^2 := by
  rcases h₀ with ⟨ha, hb⟩
  have hab : 0 < a+b := add_pos ha hb
  have hd : 0 < a^2*b^2*(a+b)^2 := by positivity
  have he₁ : (1/a^2+1/b^2)*(a^2*b^2*(a+b)^2) = (a^2+b^2)*(a+b)^2 := by
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hab] <;> ring
  have he₂ : (8/(a+b)^2)*(a^2*b^2*(a+b)^2) = 8*a^2*b^2 := by
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hab] <;> ring
  apply (mul_le_mul_iff_left₀ hd).mp
  rw [he₁, he₂]
  have hp : 0 ≤ a^2+4*a*b+b^2 := by positivity
  nlinarith [mul_nonneg (sq_nonneg (a-b)) hp]
