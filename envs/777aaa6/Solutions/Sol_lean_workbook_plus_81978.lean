-- Prove2me | solution 1 for lean_workbook_plus_81978
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:37:42.223851+00:00
-- url     : https://prove2.me/submissions/d266aee9-0234-47b0-8146-eb0a16604637

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) :
    (a-b)^2/(a+b) + (c-d)^2/(c+d) ≥ (a+c-b-d)^2/(a+b+c+d) := by
  have hab : 0 < a+b := add_pos ha hb
  have hcd : 0 < c+d := add_pos hc hd
  have hall : 0 < a+b+c+d := by linarith
  have hid : (a-b)^2/(a+b) + (c-d)^2/(c+d) - (a+c-b-d)^2/(a+b+c+d) =
      ((a-b)*(c+d)-(c-d)*(a+b))^2 / ((a+b)*(c+d)*(a+b+c+d)) := by
    field_simp [ne_of_gt hab, ne_of_gt hcd, ne_of_gt hall]
    <;> ring
  have hn : 0 ≤ (a-b)^2/(a+b) + (c-d)^2/(c+d) - (a+c-b-d)^2/(a+b+c+d) := by
    rw [hid]
    positivity
  linarith
