-- Prove2me | solution 1 for lean_workbook_plus_76609
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:08:44.082027+00:00
-- url     : https://prove2.me/submissions/a50dbdd2-ca72-4fbc-a5b0-46da3f8e195c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    (a / (b + c) + 1 / 2) * (b / (c + a) + 1 / 2) * (c / (a + b) + 1 / 2) ≥ 1 := by
  have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  have hbc : b + c ≠ 0 := ne_of_gt (add_pos hb hc)
  have hca : c + a ≠ 0 := ne_of_gt (add_pos hc ha)
  have hid : (a / (b + c) + 1 / 2) * (b / (c + a) + 1 / 2) *
      (c / (a + b) + 1 / 2) - 1 =
      ((a - b) ^ 2 * (a + b) + (b - c) ^ 2 * (b + c) +
        (c - a) ^ 2 * (c + a)) / (8 * (a + b) * (b + c) * (c + a)) := by
    field_simp
    ring
  have hnonneg : 0 ≤ ((a - b) ^ 2 * (a + b) + (b - c) ^ 2 * (b + c) +
      (c - a) ^ 2 * (c + a)) / (8 * (a + b) * (b + c) * (c + a)) := by positivity
  linarith
