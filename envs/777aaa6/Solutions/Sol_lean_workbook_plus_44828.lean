-- Prove2me | solution 1 for lean_workbook_plus_44828
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:14:11.231862+00:00
-- url     : https://prove2.me/submissions/995bdebf-c337-4ec7-b85a-7806787e37bb

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) : 4 * (a * b * c + 1) ≥ (1 + a) * (1 + b) * (1 + c)   := by
  have h1 : 0 ≤ (a - 1) * (b - 1) * (c + 1) :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb))
      (by linarith only [hc])
  have h2 : 0 ≤ (b - 1) * (c - 1) * (a + 1) :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hc))
      (by linarith only [ha])
  have h3 : 0 ≤ (c - 1) * (a - 1) * (b + 1) :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr ha))
      (by linarith only [hb])
  nlinarith only [h1, h2, h3]

#print axioms solution
