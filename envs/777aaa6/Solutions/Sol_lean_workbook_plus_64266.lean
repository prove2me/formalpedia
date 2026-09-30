-- Prove2me | solution 1 for lean_workbook_plus_64266
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:02:06.738316+00:00
-- url     : https://prove2.me/submissions/d8beb72a-bd33-40d8-bc30-bfe1e4d0c06d

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

private theorem harmonic_formula (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) : 3/(1/a+1/b+1/c) = 3*a*b*c/(a*b+b*c+c*a) := by
  have hq : 0 < a*b+b*c+c*a := by positivity
  have hs : 0 < 1/a+1/b+1/c := by positivity
  field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc, ne_of_gt hq, ne_of_gt hs]
  <;> ring

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3/(1/(a+1)+1/(b+1)+1/(c+1)) ≥ 1+3/(1/a+1/b+1/c) := by
  rw [harmonic_formula (a+1) (b+1) (c+1) (by positivity) (by positivity)
    (by positivity), harmonic_formula a b c ha hb hc]
  let q := a*b+b*c+c*a
  let r := (a+1)*(b+1)+(b+1)*(c+1)+(c+1)*(a+1)
  have hq : 0 < q := by dsimp [q]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hid : 3*(a+1)*(b+1)*(c+1)/r-(1+3*a*b*c/q) =
      ((a*b-b*c)^2+(b*c-c*a)^2+(c*a-a*b)^2+
        a*(b-c)^2+b*(c-a)^2+c*(a-b)^2)/(q*r) := by
    field_simp [ne_of_gt hq, ne_of_gt hr]
    <;> dsimp [q, r] <;> ring
  change 1+3*a*b*c/q ≤ 3*(a+1)*(b+1)*(c+1)/r
  apply sub_nonneg.mp
  rw [hid]
  positivity
