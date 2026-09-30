-- Prove2me | solution 1 for lean_workbook_plus_71827
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:02:10.172809+00:00
-- url     : https://prove2.me/submissions/d486faba-67f4-4dd4-ad7c-e13113a72cae

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a + 1) / (a ^ 2 + a + 1) + (b + 1) / (b ^ 2 + b + 1) +
      (c + 1) / (c ^ 2 + c + 1) ≤ 2 := by
  have hA : 0 < a ^ 2 + a + 1 := by positivity
  have hB : 0 < b ^ 2 + b + 1 := by positivity
  have hC : 0 < c ^ 2 + c + 1 := by positivity
  have hid : 2 - ((a + 1) / (a ^ 2 + a + 1) + (b + 1) / (b ^ 2 + b + 1) +
      (c + 1) / (c ^ 2 + c + 1)) =
      ((a*b-b*c)^2 + (b*c-c*a)^2 + (c*a-a*b)^2 +
        2*(a*b*c-1)*(a+b+c+a*b+b*c+c*a+2*a*b*c+1)) /
      (2*(a^2+a+1)*(b^2+b+1)*(c^2+c+1)) := by
    field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hC] <;> ring
  rw [habc] at hid
  simp only [sub_self, mul_zero, zero_mul, add_zero] at hid
  have hp : 0 ≤ ((a*b-b*c)^2 + (b*c-c*a)^2 + (c*a-a*b)^2) /
      (2*(a^2+a+1)*(b^2+b+1)*(c^2+c+1)) := by positivity
  rw [← hid] at hp
  linarith

#print axioms solution
