-- Prove2me | solution 1 for lean_workbook_plus_82846
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:06:03.797876+00:00
-- url     : https://prove2.me/submissions/7ed5972a-97df-4f93-bb2d-c57f15d670e8

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : 0 < a ∧ 0 < b ∧ 0 < c) :
    a / (b + c) + b / (a + c) + c / (a + b) ≥ 1.5 := by
  rcases h with ⟨ha, hb, hc⟩
  have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  have hbc : b + c ≠ 0 := ne_of_gt (add_pos hb hc)
  have hac : a + c ≠ 0 := ne_of_gt (add_pos ha hc)
  have hid : a / (b + c) + b / (a + c) + c / (a + b) - 1.5 =
      ((a - b) ^ 2 * (a + b) + (b - c) ^ 2 * (b + c) +
        (c - a) ^ 2 * (c + a)) / (2 * (a + b) * (b + c) * (a + c)) := by
    field_simp
    ring
  have hnonneg : 0 ≤ ((a - b) ^ 2 * (a + b) + (b - c) ^ 2 * (b + c) +
      (c - a) ^ 2 * (c + a)) / (2 * (a + b) * (b + c) * (a + c)) := by positivity
  linarith
