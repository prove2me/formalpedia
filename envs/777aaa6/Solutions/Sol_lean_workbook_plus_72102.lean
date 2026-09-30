-- Prove2me | solution 1 for lean_workbook_plus_72102
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:56:44.600568+00:00
-- url     : https://prove2.me/submissions/f76c1473-8b80-4a4f-83e1-133c01c39998

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a/(a+2*(b+c)) + b/(b+2*(c+a)) + c/(c+2*(a+b)) ≥ 3/5 := by
  let A := a+2*(b+c)
  let B := b+2*(c+a)
  let C := c+2*(a+b)
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hid : a/A + b/B + c/C - 3/5 =
      (2/5)*((a-b)^2/(A*B) + (b-c)^2/(B*C) + (c-a)^2/(C*A)) := by
    field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hC]
    <;> dsimp [A, B, C] <;> ring
  change 3/5 ≤ a/A + b/B + c/C
  apply sub_nonneg.mp
  rw [hid]
  positivity
