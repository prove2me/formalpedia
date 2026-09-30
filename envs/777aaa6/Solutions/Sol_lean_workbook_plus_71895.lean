-- Prove2me | solution 1 for lean_workbook_plus_71895
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:58:09.688337+00:00
-- url     : https://prove2.me/submissions/207d51c7-3269-46e0-b409-cfb2ad8c84bd

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c) / (1 + a + b + c) ≥
      a / (1 + 3 * a) + b / (1 + 3 * b) + c / (1 + 3 * c) := by
  have hA : 0 < 1 + 3 * a := by positivity
  have hB : 0 < 1 + 3 * b := by positivity
  have hC : 0 < 1 + 3 * c := by positivity
  have hS : 0 < 1 + a + b + c := by positivity
  have hid : (a + b + c) / (1 + a + b + c) -
      (a / (1 + 3 * a) + b / (1 + 3 * b) + c / (1 + 3 * c)) =
      ((1 + 3 * a) * (b - c) ^ 2 + (1 + 3 * b) * (c - a) ^ 2 +
        (1 + 3 * c) * (a - b) ^ 2) /
      ((1 + a + b + c) * (1 + 3 * a) * (1 + 3 * b) * (1 + 3 * c)) := by
    field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hC, ne_of_gt hS] <;> ring
  have hp : 0 ≤ ((1 + 3 * a) * (b - c) ^ 2 + (1 + 3 * b) * (c - a) ^ 2 +
        (1 + 3 * c) * (a - b) ^ 2) /
      ((1 + a + b + c) * (1 + 3 * a) * (1 + 3 * b) * (1 + 3 * c)) := by
    positivity
  rw [← hid] at hp
  linarith

#print axioms solution
