-- Prove2me | solution 1 for lean_workbook_plus_70131
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:56:43.411281+00:00
-- url     : https://prove2.me/submissions/f1b19891-fa4b-4f72-adca-e989e078c32c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (5*a+c)/(b+c) + 6*b/(c+a) + (5*c+a)/(a+b) ≥ 9 := by
  have hab : 0 < a+b := add_pos ha hb
  have hbc : 0 < b+c := add_pos hb hc
  have hca : 0 < c+a := add_pos hc ha
  have hmid : 0 < c+a+2*b := by positivity
  have hid : (5*a+c)/(b+c) + 6*b/(c+a) + (5*c+a)/(a+b) - 9 =
      (5*(c+a)+4*b)*(a-c)^2 / ((a+b)*(b+c)*(c+a+2*b)) +
      3*(c+a-2*b)^2 / ((c+a)*(c+a+2*b)) := by
    field_simp [ne_of_gt hab, ne_of_gt hbc, ne_of_gt hca, ne_of_gt hmid]
    <;> ring
  apply sub_nonneg.mp
  rw [hid]
  positivity
