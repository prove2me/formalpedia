-- Prove2me | solution 1 for lean_workbook_plus_70401
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:56:45.615414+00:00
-- url     : https://prove2.me/submissions/c40590c8-ed70-4b95-ad7a-d083ddf4a0a0

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a/(2*b) + (a+b)/(c+a) + (b+c)/(a+b) ≥ 5/2 := by
  have hab : 0 < a+b := add_pos ha hb
  have hca : 0 < c+a := add_pos hc ha
  have htwo : 0 < 2*b := by positivity
  have hid : a/(2*b) + (a+b)/(c+a) + (b+c)/(a+b) - 5/2 =
      (a-b)^2/(2*b*(a+b)) + (b-c)^2/((c+a)*(a+b)) := by
    field_simp [ne_of_gt hab, ne_of_gt hca, ne_of_gt htwo, ne_of_gt hb]
    <;> ring
  apply sub_nonneg.mp
  rw [hid]
  positivity
