-- Prove2me | solution 1 for lean_workbook_plus_53618
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:12:31.610501+00:00
-- url     : https://prove2.me/submissions/181a77ba-042e-4473-8543-d2fcf9fa8dbd

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a ≠ b) (hbc : b ≠ c) (hca : a ≠ c) : a^2 * (b + c) + b^2 * (c + a) + c^2 * (a + b) < 2 * (a^3 + b^3 + c^3)   := by
  have h1 : 0 < (a - b) ^ 2 * (a + b) :=
    mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hab)) (add_pos ha hb)
  have h2 : 0 ≤ (b - c) ^ 2 * (b + c) :=
    mul_nonneg (sq_nonneg _) (add_pos hb hc).le
  have h3 : 0 ≤ (c - a) ^ 2 * (c + a) :=
    mul_nonneg (sq_nonneg _) (add_pos hc ha).le
  nlinarith only [h1, h2, h3]

#print axioms solution
