-- Prove2me | solution 1 for lean_workbook_plus_72394
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:02:01.504302+00:00
-- url     : https://prove2.me/submissions/408b89db-266a-478d-a2bd-a68207bfd7bd

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (b + c) / (a ^ 2 + b * c) + (a + c) / (b ^ 2 + a * c) +
      (b + a) / (c ^ 2 + b * a) ≤ 1 / a + 1 / b + 1 / c := by
  have hA : 0 < a ^ 2 + b * c := by positivity
  have hB : 0 < b ^ 2 + a * c := by positivity
  have hC : 0 < c ^ 2 + b * a := by positivity
  have hid : 1 / a + 1 / b + 1 / c -
      ((b + c) / (a ^ 2 + b * c) + (a + c) / (b ^ 2 + a * c) +
        (b + a) / (c ^ 2 + b * a)) =
      (((a*b)^2 - (b*c)^2)^2 + ((b*c)^2 - (c*a)^2)^2 +
        ((c*a)^2 - (a*b)^2)^2) /
      (2*a*b*c*(a^2+b*c)*(b^2+a*c)*(c^2+b*a)) := by
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc,
      ne_of_gt hA, ne_of_gt hB, ne_of_gt hC] <;> ring
  have hp : 0 ≤ (((a*b)^2 - (b*c)^2)^2 + ((b*c)^2 - (c*a)^2)^2 +
        ((c*a)^2 - (a*b)^2)^2) /
      (2*a*b*c*(a^2+b*c)*(b^2+a*c)*(c^2+b*a)) := by positivity
  rw [← hid] at hp
  linarith

#print axioms solution
