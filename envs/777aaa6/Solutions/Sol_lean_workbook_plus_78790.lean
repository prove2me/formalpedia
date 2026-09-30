-- Prove2me | solution 1 for lean_workbook_plus_78790
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:25:26.075824+00:00
-- url     : https://prove2.me/submissions/416a281a-7445-41fd-a02a-dc17729a5828

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    4 / (a ^ 2 + b * c) ≤ 1 / a ^ 2 + 1 / (b * c) := by
  have haa : 0 < a ^ 2 := by positivity
  have hbc : 0 < b * c := mul_pos hb hc
  have hs : 0 < a ^ 2 + b * c := add_pos haa hbc
  have identity :
      1 / a ^ 2 + 1 / (b * c) - 4 / (a ^ 2 + b * c) =
        (a ^ 2 - b * c) ^ 2 / (a ^ 2 * (b * c) * (a ^ 2 + b * c)) := by
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc, ne_of_gt hs]
    <;> ring
  have : 0 ≤ (a ^ 2 - b * c) ^ 2 / (a ^ 2 * (b * c) * (a ^ 2 + b * c)) := by positivity
  linarith

#print axioms solution
