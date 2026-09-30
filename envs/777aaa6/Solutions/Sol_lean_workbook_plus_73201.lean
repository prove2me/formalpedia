-- Prove2me | solution 1 for lean_workbook_plus_73201
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:59:28.457993+00:00
-- url     : https://prove2.me/submissions/0ffdd474-2684-4df3-91a7-cf718afba430

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) : (1 / (1 + a) + 1 / (1 + b)) ≤ (1 / 2 + 1 / (1 + a * b))   := by
  have hab : 1 ≤ a * b := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  have hda : 0 < 1 + a := by linarith only [ha]
  have hdb : 0 < 1 + b := by linarith only [hb]
  have hdab : 0 < 1 + a * b := by linarith only [hab]
  have hnum : 0 ≤ (a - 1) * (b - 1) * (a * b - 1) :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)) (sub_nonneg.mpr hab)
  have hden : 0 < 2 * (1 + a) * (1 + b) * (1 + a * b) := by positivity
  have hfrac := div_nonneg hnum hden.le
  have hidentity : (1 / 2 + 1 / (1 + a * b)) - (1 / (1 + a) + 1 / (1 + b)) =
      ((a - 1) * (b - 1) * (a * b - 1)) / (2 * (1 + a) * (1 + b) * (1 + a * b)) := by
    field_simp [ne_of_gt hda, ne_of_gt hdb, ne_of_gt hdab] <;> ring
  rw [← hidentity] at hfrac
  exact sub_nonneg.mp hfrac

#print axioms solution
