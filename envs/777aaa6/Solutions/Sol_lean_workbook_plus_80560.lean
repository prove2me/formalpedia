-- Prove2me | solution 1 for lean_workbook_plus_80560
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:02:57.743855+00:00
-- url     : https://prove2.me/submissions/087e0108-aba0-4437-b307-def6f31df52e

import Mathlib

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    b * c / (a ^ 2 + 2 * b * c) + a * c / (b ^ 2 + 2 * a * c) +
      a * b / (c ^ 2 + 2 * a * b) ≤ 1 := by
  have hA : 0 < a ^ 2 + 2 * b * c := by positivity
  have hB : 0 < b ^ 2 + 2 * a * c := by positivity
  have hC : 0 < c ^ 2 + 2 * a * b := by positivity
  have hcert : 0 ≤ (a * b + a * c + b * c) *
      ((a * b - a * c) ^ 2 + (a * c - b * c) ^ 2 + (b * c - a * b) ^ 2) := by
    positivity
  calc
    _ = (b * c * (b ^ 2 + 2 * a * c) * (c ^ 2 + 2 * a * b) +
        a * c * (a ^ 2 + 2 * b * c) * (c ^ 2 + 2 * a * b) +
        a * b * (a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * a * c)) /
        ((a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * a * c) * (c ^ 2 + 2 * a * b)) := by
      field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hC]
      <;> ring
    _ ≤ 1 := (div_le_one (mul_pos (mul_pos hA hB) hC)).2 (by nlinarith only [hcert])

#print axioms solution
