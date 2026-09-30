-- Prove2me | solution 1 for lean_workbook_plus_65765
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:57:32.197615+00:00
-- url     : https://prove2.me/submissions/f7c368ee-76f4-43da-b0e6-9780cca2e7d4

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (4 * a + 11 * b) / (6 * a + 13 * b + c) +
      (4 * b + 11 * c) / (a + 6 * b + 13 * c) +
      (4 * c + 11 * a) / (13 * a + b + 6 * c) ≤ 9 / 4 := by
  let A := 6 * a + 13 * b + c
  let B := a + 6 * b + 13 * c
  let C := 13 * a + b + 6 * c
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  let S := a * (81 * (a + 4 * b - 5 * c) ^ 2 +
      230 * (a - b) ^ 2 + 1069 * (a - c) ^ 2) +
    b * (81 * (b + 4 * c - 5 * a) ^ 2 +
      230 * (b - c) ^ 2 + 1069 * (b - a) ^ 2) +
    c * (81 * (c + 4 * a - 5 * b) ^ 2 +
      230 * (c - a) ^ 2 + 1069 * (c - b) ^ 2)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hid : 9 / 4 - ((4 * a + 11 * b) / A +
      (4 * b + 11 * c) / B + (4 * c + 11 * a) / C) =
      S / (24 * A * B * C) := by
    field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hC]
    dsimp [A, B, C, S]
    ring
  have hnonneg : 0 ≤ S / (24 * A * B * C) := div_nonneg hS (by positivity)
  change (4 * a + 11 * b) / A + (4 * b + 11 * c) / B +
    (4 * c + 11 * a) / C ≤ 9 / 4
  linarith

#print axioms solution
