-- Prove2me | solution 1 for lean_workbook_plus_79039
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:48:58.18599+00:00
-- url     : https://prove2.me/submissions/97df89d0-4ab3-4312-83da-042b2f5c424a

import Mathlib
set_option autoImplicit false

theorem solution (a b p q : ℕ) : a = p * q + p ^ 2 ∧ b = p * q + q ^ 2 → √(a + b) = p + q   := by
  rintro ⟨ha, hb⟩
  have hs : (a : ℝ) + (b : ℝ) = ((p : ℝ) + (q : ℝ)) ^ 2 := by
    rw [ha, hb]
    push_cast
    ring
  rw [hs, Real.sqrt_sq (show 0 ≤ (p : ℝ) + (q : ℝ) by positivity)]

#print axioms solution
