-- Prove2me | solution 2 for lean_workbook_plus_76663
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:34:02.635515+00:00
-- url     : https://prove2.me/submissions/b666c299-e808-47c1-ba32-83b1e449b7f4

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

theorem solution (a b : ℝ) (hab : a * b = 1) (ha : 0 < a) (hb : 0 < b) :
    1 / (a ^ 2 + b) + 1 / (b + 1) ≤ 1 := by
  have h1 : 0 < a^2 + b := by positivity
  have h2 : 0 < b + 1 := by positivity
  have hab2 : a^2 * b^2 = 1 := by
    nlinarith only [congrArg (fun x : ℝ => x^2) hab]
  have hid : 1 - (1 / (a^2 + b) + 1 / (b + 1)) =
      (b - 1)^2 * (b + 1) / (b * (a^2 + b) * (b + 1)) := by
    field_simp [ne_of_gt hb, ne_of_gt h1, ne_of_gt h2]
    linear_combination hab2
  have hn : 0 ≤ (b - 1)^2 * (b + 1) / (b * (a^2 + b) * (b + 1)) := by
    positivity
  linarith only [hid, hn]
