-- Prove2me | solution 1 for lean_workbook_plus_30097
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:55:43.5757+00:00
-- url     : https://prove2.me/submissions/604e9608-5ae7-46db-847e-eaa6428d53c2

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (hab : 1 ≤ a) (hbc : 2 ≤ b) (hca : 3 ≤ c) (habc : a * b + b * c + c * a = 16) : a * b * c ≤ 12   := by
  have ha0 : 0 ≤ a := by linarith only [hab]
  have hb0 : 0 ≤ b := by linarith only [hbc]
  have hbc6 : 6 ≤ b * c := by
    nlinarith only [hbc, hca, mul_nonneg (sub_nonneg.mpr hbc) (sub_nonneg.mpr hca)]
  have hab2a : 2 * a ≤ a * b := by
    nlinarith only [mul_nonneg ha0 (sub_nonneg.mpr hbc)]
  have hca3a : 3 * a ≤ c * a := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hca) ha0]
  have ha2 : a ≤ 2 := by nlinarith only [habc, hbc6, hab2a, hca3a]
  have hab2 : 2 ≤ a * b := by
    nlinarith only [hab, hbc, mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hbc)]
  have hcb3b : 3 * b ≤ b * c := by
    nlinarith only [mul_nonneg hb0 (sub_nonneg.mpr hca)]
  have hsum : a + b ≤ 5 := by nlinarith only [habc, hab2, hca3a, hcb3b]
  have hp : 0 ≤ (c - 3) * (5 - a - b) :=
    mul_nonneg (sub_nonneg.mpr hca) (by linarith only [hsum])
  have hq : 0 ≤ (2 - a) * (b - 2) :=
    mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hbc)
  have hr : 0 ≤ (2 - a) * (b - 2) * (c - 3) :=
    mul_nonneg hq (sub_nonneg.mpr hca)
  have hid : 5 * (12 - a * b * c) =
      4 * ((c - 3) * (5 - a - b)) + 9 * ((2 - a) * (b - 2)) +
        5 * ((2 - a) * (b - 2) * (c - 3)) := by
    linear_combination -6 * habc
  nlinarith only [hid, hp, hq, hr]

#print axioms solution
