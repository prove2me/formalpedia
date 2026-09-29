-- Prove2me | solution 1 for lean_workbook_plus_72669
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:50:36.462945+00:00
-- url     : https://prove2.me/submissions/3ece8fd4-c7d5-43cf-a965-33d1fa778d2d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 1 / a + 1 / b = 1) : 1 / (a + 1) + 2 / (2 * b + 1) ≤ 3 / 4   := by
  have he : a + b = a * b := by
    have he := hab
    field_simp [ne_of_gt ha, ne_of_gt hb] at he
    nlinarith only [he]
  have ha1 : 0 < a - 1 := by
    by_contra hn
    have hm := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hb) (le_of_not_gt hn)
    nlinarith only [he, hm, ha]
  have hprod : 0 ≤ (a - 1) * (a + 4 * b - 9) := by
    nlinarith only [sq_nonneg (a - 3), he]
  have hn : 0 ≤ a + 4 * b - 9 := nonneg_of_mul_nonneg_right hprod ha1
  have hd1 : 0 < a + 1 := by positivity
  have hd2 : 0 < 2 * b + 1 := by positivity
  have hid : 3 / 4 - (1 / (a + 1) + 2 / (2 * b + 1)) =
      (a + 4 * b - 9) / (4 * (a + 1) * (2 * b + 1)) := by
    field_simp
    nlinarith only [he]
  have hgap : 0 ≤ (a + 4 * b - 9) / (4 * (a + 1) * (2 * b + 1)) :=
    div_nonneg hn (by positivity)
  linarith only [hid, hgap]
