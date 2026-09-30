-- Prove2me | solution 1 for lean_workbook_plus_26074
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:05:55.302285+00:00
-- url     : https://prove2.me/submissions/4d9931d3-08d3-442f-a851-8df96f901f6c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : 1 / a + 1 / b = 1) :
    1 / 4 ≤ 1 / (a * (a + 2)) + 1 / (b * (b + 2)) ∧
    1 / (a * (a + 2)) + 1 / (b * (b + 2)) < 1 / 3 := by
  field_simp [ne_of_gt ha, ne_of_gt hb] at hab
  have hs : 0 < a + b := add_pos ha hb
  have hfour : 4 ≤ a + b := by
    by_contra hn
    have hp := mul_pos hs (sub_pos.2 (lt_of_not_ge hn))
    nlinarith [sq_nonneg (a - b)]
  have ha2 : 0 < a + 2 := by linarith
  have hb2 : 0 < b + 2 := by linarith
  have hd : 0 < 3 * (a + b) + 4 := by linarith
  have hid : 1 / (a * (a + 2)) + 1 / (b * (b + 2)) =
      (a + b) / (3 * (a + b) + 4) := by
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt ha2, ne_of_gt hb2, ne_of_gt hd]
    linear_combination
      ((a + b) * (a * b) + 3 * (a + b) ^ 2 + 10 * (a + b) + 8) * hab
  rw [hid]
  constructor
  · apply (le_div_iff₀ hd).2
    linarith
  · apply (div_lt_iff₀ hd).2
    linarith
