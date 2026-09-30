-- Prove2me | solution 1 for lean_workbook_plus_53794
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:12:32.909415+00:00
-- url     : https://prove2.me/submissions/00f3e318-6e00-4c37-a643-6ab00a0c37c4

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a^2 + 2 * b^2 + 2 * c^2 = a^3 + 2 * b^3 + 2 * c^3) : a + 2 * b + 2 * c ≤ 5   := by
  have pa : 0 ≤ (a - 1) ^ 2 * (a + 1) :=
    mul_nonneg (sq_nonneg _) (by linarith only [ha])
  have pb : 0 ≤ (b - 1) ^ 2 * (b + 1) :=
    mul_nonneg (sq_nonneg _) (by linarith only [hb])
  have pc : 0 ≤ (c - 1) ^ 2 * (c + 1) :=
    mul_nonneg (sq_nonneg _) (by linarith only [hc])
  nlinarith only [hab, pa, pb, pc]

#print axioms solution
