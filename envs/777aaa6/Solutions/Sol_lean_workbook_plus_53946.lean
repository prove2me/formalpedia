-- Prove2me | solution 1 for lean_workbook_plus_53946
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:12:34.334511+00:00
-- url     : https://prove2.me/submissions/18adf4b7-d771-4bb3-a94c-f6e0ba46bf35

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) : a / (b + 1) + b / (a + 1) ≤ 1   := by
  have hda : 0 < a + 1 := by linarith only [ha.1]
  have hdb : 0 < b + 1 := by linarith only [hb.1]
  have hn : 0 ≤ a * (1 - a) + b * (1 - b) + (1 - a) * (1 - b) :=
    add_nonneg
      (add_nonneg (mul_nonneg ha.1 (sub_nonneg.mpr ha.2))
        (mul_nonneg hb.1 (sub_nonneg.mpr hb.2)))
      (mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hb.2))
  have hid : 1 - (a / (b + 1) + b / (a + 1)) =
      (a * (1 - a) + b * (1 - b) + (1 - a) * (1 - b)) /
        ((a + 1) * (b + 1)) := by
    field_simp [ne_of_gt hda, ne_of_gt hdb] <;> ring
  apply sub_nonneg.mp
  rw [hid]
  exact div_nonneg hn (mul_nonneg hda.le hdb.le)

#print axioms solution
