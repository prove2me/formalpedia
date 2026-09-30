-- Prove2me | solution 1 for lean_workbook_plus_82362
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:28:42.571887+00:00
-- url     : https://prove2.me/submissions/457cb802-b1dd-4a2f-bf7c-9b1369230c64

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b - c) / (a + b + 3 * c) + (b + c - a) / (3 * a + b + c) +
      (c + a - b) / (a + 3 * b + c) ≥ 3 / 5 := by
  have hd₁ : 0 < a + b + 3 * c := by positivity
  have hd₂ : 0 < 3 * a + b + c := by positivity
  have hd₃ : 0 < a + 3 * b + c := by positivity
  have identity :
      (a + b - c) / (a + b + 3 * c) + (b + c - a) / (3 * a + b + c) +
        (c + a - b) / (a + 3 * b + c) - 3 / 5 =
      (8 / 5) * ((a - b) ^ 2 * (a + b + 3 * c) +
        (b - c) ^ 2 * (3 * a + b + c) + (c - a) ^ 2 * (a + 3 * b + c)) /
        ((a + b + 3 * c) * (3 * a + b + c) * (a + 3 * b + c)) := by
    field_simp [ne_of_gt hd₁, ne_of_gt hd₂, ne_of_gt hd₃]
    <;> ring
  have : 0 ≤
      (8 / 5 : ℝ) * ((a - b) ^ 2 * (a + b + 3 * c) +
        (b - c) ^ 2 * (3 * a + b + c) + (c - a) ^ 2 * (a + 3 * b + c)) /
        ((a + b + 3 * c) * (3 * a + b + c) * (a + 3 * b + c)) := by positivity
  linarith

#print axioms solution
