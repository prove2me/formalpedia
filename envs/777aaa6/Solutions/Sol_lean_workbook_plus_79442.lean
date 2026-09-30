-- Prove2me | solution 1 for lean_workbook_plus_79442
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:48:08.168706+00:00
-- url     : https://prove2.me/submissions/26571097-41ab-4579-a2b0-3b68c7235b96

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem solution (a b c : ℝ)
    (ha : 3 / 2 ≤ a) (hb : 3 / 2 ≤ b) (hc : 3 / 2 ≤ c) :
    a + 2 * b + 3 * c ≥ 27 / 16 * (1 / a - 2 / b + 3 / c + 4) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  have hid : a + 2 * b + 3 * c - 27 / 16 * (1 / a - 2 / b + 3 / c + 4) =
      (a - 3 / 2) * (a + 9 / 8) / a +
      (b - 3 / 2) * (2 * b - 9 / 4) / b +
      3 * (c - 3 / 2) * (c + 9 / 8) / c := by
    field_simp [ne_of_gt ha0, ne_of_gt hb0, ne_of_gt hc0]
    ring
  have hpa : 0 ≤ (a - 3 / 2) * (a + 9 / 8) / a :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr ha) (by linarith)) ha0.le
  have hpb : 0 ≤ (b - 3 / 2) * (2 * b - 9 / 4) / b :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hb) (by linarith)) hb0.le
  have hpc : 0 ≤ 3 * (c - 3 / 2) * (c + 9 / 8) / c :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hc))
      (by linarith)) hc0.le
  linarith
