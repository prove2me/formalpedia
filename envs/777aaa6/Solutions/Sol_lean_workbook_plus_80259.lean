-- Prove2me | solution 1 for lean_workbook_plus_80259
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:21:34.959836+00:00
-- url     : https://prove2.me/submissions/e9be2059-bc4f-4772-83ab-8b5f7db085ca

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem solution {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    (1 / 2) * (a ^ 2 + b ^ 2 + c ^ 2 + (9 * a * b * c) / (a + b + c) -
      2 * a * b - 2 * b * c - 2 * c * a) +
      (7 / 4) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) ≥ 0 := by
  have hs : 0 < a + b + c := by positivity
  have identity :
      (2 * (a + b + c)) *
        ((1 / 2) * (a ^ 2 + b ^ 2 + c ^ 2 + (9 * a * b * c) / (a + b + c) -
          2 * a * b - 2 * b * c - 2 * c * a) +
          (7 / 4) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2)) =
        3 * (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) +
          (a - b) ^ 2 * (a + b) + (b - c) ^ 2 * (b + c) +
          (c - a) ^ 2 * (c + a) := by
    field_simp [ne_of_gt hs]
    <;> ring
  apply nonneg_of_mul_nonneg_right (a := 2 * (a + b + c))
    (by rw [identity]; positivity) (by positivity)

#print axioms solution
