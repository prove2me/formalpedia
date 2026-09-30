-- Prove2me | solution 1 for lean_workbook_plus_61400
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:55:46.808801+00:00
-- url     : https://prove2.me/submissions/a2cb8ca7-3b71-4e66-b18c-f2a163e4368e

import Mathlib
set_option autoImplicit false

theorem solution (a b c x y z : ℝ) (h1 : a ≥ b ∧ b ≥ c) (h2 : x ≥ y ∧ y ≥ z) (h3 : x + y + z = 0) : a * x + b * y + c * z ≥ 0   := by
  rcases h1 with ⟨hab, hbc⟩
  rcases h2 with ⟨hxy, hyz⟩
  have hx : 0 ≤ x := by linarith
  have hz : z ≤ 0 := by linarith
  have hp := mul_nonneg (sub_nonneg.mpr hab) hx
  have hq := mul_nonneg (sub_nonneg.mpr hbc) (neg_nonneg.mpr hz)
  calc
    0 ≤ (a - b) * x + (b - c) * (-z) := add_nonneg hp hq
    _ = a * x + b * y + c * z := by
      have hy : y = -x - z := by linarith
      rw [hy]
      ring

#print axioms solution
